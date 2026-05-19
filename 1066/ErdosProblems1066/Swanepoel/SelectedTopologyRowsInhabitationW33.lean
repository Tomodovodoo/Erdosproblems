import ErdosProblems1066.Swanepoel.ExtractedComponentsConcreteClosureW32
import ErdosProblems1066.Swanepoel.FaceBoundaryTopologySourceW32
import ErdosProblems1066.Swanepoel.JordanBoundaryConcreteInhabitationW24
import ErdosProblems1066.Swanepoel.BoundaryAngleTurnW11

set_option autoImplicit false

/-!
# W33 selected-topology row inhabitance

This file turns the honest W32 minimal-failure selected-topology source into
actual indexed row families.  The rows are only selected for minimal cleared
failures, and the final actual selected-topology rows are obtained through the
W32 concrete row adapters.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SelectedTopologyRowsInhabitationW33

universe u

noncomputable section

open ExtractedComponentsConcreteClosureW32

variable {n : Nat}

abbrev MinimalFailureSelectedTopologySourceTarget : Prop :=
  MinimalFailureSelectedTopologySourceW32.MinimalFailureSelectedTopologySourceTarget

abbrev MinimalFailureNondegenerateMissingTopologyFactsTarget : Prop :=
  FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget

abbrev MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget : Prop :=
  FaceBoundaryTopologySourceW32.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget

abbrev MinimalFailureExactActualTopologyFieldsTarget : Prop :=
  FaceBoundaryTopologySourceW32.MinimalFailureExactActualTopologyFieldsTarget

abbrev MinimalFailureActualOuterBoundaryCycleDataRows :=
  FaceBoundaryTopologySourceW32.MinimalFailureActualOuterBoundaryCycleDataRows

abbrev MinimalBoundaryTopologyWitnessFamily :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.{u}

abbrev MinimalBoundaryTopologySkeleton
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologySkeleton.{u}
    C hmin

abbrev MinimalBoundaryTopologySkeletonFamily :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}

abbrev MinimalBoundaryTopologyMissingLongArcTriangleRunField
    (S : MinimalBoundaryTopologySkeletonFamily.{u}) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.MissingLongArcTriangleRunField
    S

abbrev MinimalBoundaryTopologyLongArcFieldFamily
    (S : MinimalBoundaryTopologySkeletonFamily.{u}) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.LongArcFieldFamily
    S

abbrev MinimalBoundaryTopologyLongArcRawTurnRows
    (S : MinimalBoundaryTopologySkeletonFamily.{u}) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.LongArcRawTurnRows
    S

abbrev MinimalBoundaryTopologyTriangleRunFieldFamily
    (S : MinimalBoundaryTopologySkeletonFamily.{u}) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.TriangleRunFieldFamily
    S

abbrev MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsFamily
    (S : MinimalBoundaryTopologySkeletonFamily.{u}) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.FinitePQSpineCyclicSuccessorRowsFamily
    S

abbrev MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows
    (S : MinimalBoundaryTopologySkeletonFamily.{u}) : Type (u + 1) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
        (S.row C hmin).classification
        (S.row C hmin).geometricAngleSum
        (S.row C hmin).forced_le_geometric
        (S.row C hmin).geometric_le_polygon
        (S.row C hmin).Subpolygon
        (S.row C hmin).subpolygonData

abbrev MinimalBoundaryTopologyNoBoundaryGapTriangleDegree34Rows
    (S : MinimalBoundaryTopologySkeletonFamily.{u}) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.BoundaryLongArcNoBoundaryGapTriangleDegree34Rows
    S

/--
The non-circular finite-`p/q` successor-row theorem used by the W34
missing-field integration.  This is the W16 theorem surface over arbitrary
topology/angle/subpolygon/long-arc rows; it does not depend on the actual
component closure that W34 builds only after the missing field is available.
-/
abbrev MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem :
    Prop :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.FinitePQSpineCyclicSuccessorRowsTheorem.{u}

abbrev MinimalBoundaryTopologyExplicitM8TriangleRunIndicesTheorem :
    Prop :=
  TriangleRunSelectorW17.ExplicitM8TriangleRunIndicesTheorem.{u}

def minimalBoundaryTopologyLongArcFieldFamilyOfLongArcRawTurnRows
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (rows : MinimalBoundaryTopologyLongArcRawTurnRows.{u} S) :
    MinimalBoundaryTopologyLongArcFieldFamily S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.longArcFieldFamilyOfLongArcRawTurnRows
    S rows

theorem nonempty_minimalBoundaryTopologyLongArcFieldFamily_of_longArcRawTurnRows
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (rows : MinimalBoundaryTopologyLongArcRawTurnRows.{u} S) :
    Nonempty (MinimalBoundaryTopologyLongArcFieldFamily S) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.longArcFieldFamily_nonempty_of_longArcRawTurnRows
    S rows

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  JordanBoundaryConcreteInhabitationW24.CanonicalGraph C

abbrev ConcreteBoundaryWalkClassification
    (C : _root_.UDConfig n) (topology : ConcreteTopologyFacts C) :=
  JordanBoundaryConcreteInhabitationW24.ConcreteBoundaryWalkClassification
    C topology

abbrev BoundaryAngleTurnTopologyPackage
    {n : Nat} (C : _root_.UDConfig n) :=
  BoundaryAngleTurnW11.UDConfigRoute.BoundaryAngleTurnTopologyPackage.{u, 0}
    C

abbrev BoundaryAngleTurnTopologyPackageFamily :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      BoundaryAngleTurnTopologyPackage.{u} C

theorem nondegenerateMissingTopologyFactsTarget_of_remainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureNondegenerateMissingTopologyFactsTarget :=
  FaceBoundaryTopologySourceW32.minimalFailureNondegenerateMissingTopologyFactsTarget_of_remainingActualOuterBoundaryCycleTheoremTarget
    h

theorem remainingActualOuterBoundaryCycleTheoremTarget_of_nondegenerateMissingTopologyFactsTarget
    (h : MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget :=
  FaceBoundaryTopologySourceW32.minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_of_nonDegenerateMissingTopologyFactsTarget
    h

def remainingActualOuterBoundaryCycleTheoremTargetOfExactActualTopologyFieldsTarget
    (h : MinimalFailureExactActualTopologyFieldsTarget) :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget :=
  FaceBoundaryTopologySourceW32.minimalFailureRemainingActualCycleTarget_of_exactActualTopologyFieldsTarget
    h

theorem remainingActualOuterBoundaryCycleTheoremTarget_iff_nondegenerateMissingTopologyFactsTarget :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget <->
      MinimalFailureNondegenerateMissingTopologyFactsTarget :=
  FaceBoundaryTopologySourceW32.minimalFailureNondegenerateMissingTopologyFactsTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget.symm

def actualOuterBoundaryCycleDataRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureActualOuterBoundaryCycleDataRows :=
  FaceBoundaryTopologySourceW32.actualOuterBoundaryCycleDataRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    h

def missingTopologyFactsRowsOfNondegenerateMissingTopologyFactsTarget
    (h : MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    MinimalFailureMissingTopologyFactsRows :=
  fun C hmin => Classical.choose (h C hmin)

def topologyBoundaryRowsOfNondegenerateMissingTopologyFactsTarget
    (h : MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    MinimalFailureTopologyBoundaryRows :=
  fun C hmin =>
    (missingTopologyFactsRowsOfNondegenerateMissingTopologyFactsTarget
      h C hmin).toCore

def concreteTopologyFactsRowsOfNondegenerateMissingTopologyFactsTarget
    (h : MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    MinimalFailureConcreteTopologyFactsRows :=
  fun C hmin =>
    (actualTopologyRowsOfMissingTopologyFactsRows
      (missingTopologyFactsRowsOfNondegenerateMissingTopologyFactsTarget h)
      C hmin).toConcreteTopologyFacts

def actualSelectedTopologyRowsOfNondegenerateMissingTopologyFactsTarget
    (h : MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    MinimalFailureActualSelectedTopologyRows :=
  actualTopologyRowsOfMissingTopologyFactsRows
    (missingTopologyFactsRowsOfNondegenerateMissingTopologyFactsTarget h)

theorem remainingActualOuterBoundaryCycleTheoremTarget_iff_nonempty_actualOuterBoundaryCycleDataRows :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget <->
      Nonempty MinimalFailureActualOuterBoundaryCycleDataRows :=
  FaceBoundaryTopologySourceW32.minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_iff_nonempty_actualOuterBoundaryCycleDataRows

def missingTopologyFactsRowsOfActualOuterBoundaryCycleDataRows
    (rows : MinimalFailureActualOuterBoundaryCycleDataRows) :
    MinimalFailureMissingTopologyFactsRows :=
  fun C hmin => (rows C hmin).toMissingTopologyFacts

def topologyBoundaryRowsOfActualOuterBoundaryCycleDataRows
    (rows : MinimalFailureActualOuterBoundaryCycleDataRows) :
    MinimalFailureTopologyBoundaryRows :=
  fun C hmin => (rows C hmin).core

def concreteTopologyFactsRowsOfActualOuterBoundaryCycleDataRows
    (rows : MinimalFailureActualOuterBoundaryCycleDataRows) :
    MinimalFailureConcreteTopologyFactsRows :=
  fun C hmin =>
    JordanTopologyFactsConcrete.TopologyFacts.ofMissingTopologyFacts
      ((rows C hmin).toMissingTopologyFacts)

def missingTopologyFactsRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureMissingTopologyFactsRows :=
  missingTopologyFactsRowsOfNondegenerateMissingTopologyFactsTarget
    (nondegenerateMissingTopologyFactsTarget_of_remainingActualOuterBoundaryCycleTheoremTarget
      h)

def topologyBoundaryRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureTopologyBoundaryRows :=
  topologyBoundaryRowsOfNondegenerateMissingTopologyFactsTarget
    (nondegenerateMissingTopologyFactsTarget_of_remainingActualOuterBoundaryCycleTheoremTarget
      h)

def concreteTopologyFactsRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureConcreteTopologyFactsRows :=
  concreteTopologyFactsRowsOfNondegenerateMissingTopologyFactsTarget
    (nondegenerateMissingTopologyFactsTarget_of_remainingActualOuterBoundaryCycleTheoremTarget
      h)

def actualSelectedTopologyRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureActualSelectedTopologyRows :=
  actualSelectedTopologyRowsOfNondegenerateMissingTopologyFactsTarget
    (nondegenerateMissingTopologyFactsTarget_of_remainingActualOuterBoundaryCycleTheoremTarget
      h)

theorem selectedTopologySourceTarget_of_remainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureSelectedTopologySourceTarget :=
  minimalFailureSelectedTopologySourceTarget_of_concreteTopologyFactsRows
    (concreteTopologyFactsRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
      h)

theorem nonempty_actualSelectedTopologyRows_of_remainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    Nonempty MinimalFailureActualSelectedTopologyRows :=
  Nonempty.intro
    (actualSelectedTopologyRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
      h)

abbrev RemainingActualCycleComponentRows
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :=
  ActualTopologyRemainingComponentRows.{u}
    (actualSelectedTopologyRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
      h)

def actualTopologyClosurePackageOfRemainingActualCycleComponentRows
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (components : RemainingActualCycleComponentRows.{u} h) :
    ActualTopologyExtractedComponentClosurePackage.{u} :=
  actualTopologyClosurePackageOfActualTopologyRows
    (actualSelectedTopologyRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
      h)
    components

theorem actualTopologyClosurePackage_nonempty_of_remainingActualCycleComponentRows
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (components : RemainingActualCycleComponentRows.{u} h) :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} :=
  Nonempty.intro
    (actualTopologyClosurePackageOfRemainingActualCycleComponentRows
      h components)

structure MinimalBoundaryTopologySkeletonRemainderRows
    (topology : MinimalFailureConcreteTopologyFactsRows) :
    Type (u + 1) where
  classification :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        ConcreteBoundaryWalkClassification C (topology C hmin)
  geometricAngleSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C), Real
  forced_le_geometric :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (classification C hmin).counts.forcedBoundaryAngleSum <=
          geometricAngleSum C hmin
  geometric_le_polygon :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        geometricAngleSum C hmin <=
          (classification C hmin).counts.polygonAngleSum
  Subpolygon :
    forall {n : Nat} (C : _root_.UDConfig n)
      (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C), Type u
  subpolygonData :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Subpolygon C hmin ->
          SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)

def minimalBoundaryTopologySkeletonFamilyOfConcreteTopologyFactsRows
    (topology : MinimalFailureConcreteTopologyFactsRows)
    (rows : MinimalBoundaryTopologySkeletonRemainderRows.{u} topology) :
    MinimalBoundaryTopologySkeletonFamily.{u} where
  row := fun C hmin =>
    { topology := topology C hmin
      classification := rows.classification C hmin
      geometricAngleSum := rows.geometricAngleSum C hmin
      forced_le_geometric := rows.forced_le_geometric C hmin
      geometric_le_polygon := rows.geometric_le_polygon C hmin
      Subpolygon := rows.Subpolygon C hmin
      subpolygonData := rows.subpolygonData C hmin }

abbrev RemainingActualCycleSkeletonRemainderRows
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :=
  MinimalBoundaryTopologySkeletonRemainderRows.{u}
    (concreteTopologyFactsRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
      h)

abbrev ExactActualTopologySkeletonRemainderRows
    (h : MinimalFailureExactActualTopologyFieldsTarget) :=
  RemainingActualCycleSkeletonRemainderRows.{u}
    (remainingActualOuterBoundaryCycleTheoremTargetOfExactActualTopologyFieldsTarget
      h)

def minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (rows : RemainingActualCycleSkeletonRemainderRows.{u} h) :
    MinimalBoundaryTopologySkeletonFamily.{u} :=
  minimalBoundaryTopologySkeletonFamilyOfConcreteTopologyFactsRows
    (concreteTopologyFactsRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
      h)
    rows

/--
Exact-S2 skeleton constructor.  S3 should supply the dependent remainder rows
for the exact actual-topology target; this builds the W24 skeleton family
directly, without detouring through the witness-family nonempty bridge that
also asks for the missing long-arc/triangle-run field.
-/
def minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h) :
    MinimalBoundaryTopologySkeletonFamily.{u} :=
  minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
    (remainingActualOuterBoundaryCycleTheoremTargetOfExactActualTopologyFieldsTarget
      h)
    rows

theorem nonempty_minimalBoundaryTopologySkeletonFamily_of_remainingActualCycleSkeletonRows
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (rows : RemainingActualCycleSkeletonRemainderRows.{u} h) :
    Nonempty MinimalBoundaryTopologySkeletonFamily.{u} :=
  Nonempty.intro
    (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
      h rows)

theorem nonempty_minimalBoundaryTopologySkeletonFamily_of_exactActualTopologyFieldsTarget_s3Rows
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (s3Rows : ExactActualTopologySkeletonRemainderRows.{u} h) :
    Nonempty MinimalBoundaryTopologySkeletonFamily.{u} :=
  Nonempty.intro
    (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
      h s3Rows)

def minimalBoundaryTopologyLongArcFieldFamilyOfRemainingActualCycleSkeletonRowsRawTurnRows
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (rows : RemainingActualCycleSkeletonRemainderRows.{u} h)
    (longArcRows :
      MinimalBoundaryTopologyLongArcRawTurnRows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          h rows)) :
    MinimalBoundaryTopologyLongArcFieldFamily
      (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
        h rows) :=
  minimalBoundaryTopologyLongArcFieldFamilyOfLongArcRawTurnRows
    (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
      h rows)
    longArcRows

theorem nonempty_minimalBoundaryTopologyLongArcFieldFamily_of_remainingActualCycleSkeletonRows_rawTurnRows
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (rows : RemainingActualCycleSkeletonRemainderRows.{u} h)
    (longArcRows :
      MinimalBoundaryTopologyLongArcRawTurnRows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          h rows)) :
    Nonempty
      (MinimalBoundaryTopologyLongArcFieldFamily
        (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          h rows)) :=
  nonempty_minimalBoundaryTopologyLongArcFieldFamily_of_longArcRawTurnRows
    (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
      h rows)
    longArcRows

def minimalBoundaryTopologyWitnessFamilyOfRemainingActualCycleSkeletonRows
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (rows : RemainingActualCycleSkeletonRemainderRows.{u} h)
    (missing :
      MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          h rows)) :
    MinimalBoundaryTopologyWitnessFamily.{u} :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.ofSkeletonAndMissingField
    (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
      h rows)
    missing

theorem minimalBoundaryTopologyWitnessFamily_nonempty_of_remainingActualCycleSkeletonRows
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (rows : RemainingActualCycleSkeletonRemainderRows.{u} h)
    (missing :
      MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          h rows)) :
    Nonempty MinimalBoundaryTopologyWitnessFamily.{u} :=
  Nonempty.intro
    (minimalBoundaryTopologyWitnessFamilyOfRemainingActualCycleSkeletonRows
      h rows missing)

theorem minimalBoundaryTopologyWitnessFamily_nonempty_iff_exists_skeleton_missingLongArcTriangleRunField :
    Nonempty MinimalBoundaryTopologyWitnessFamily.{u} <->
      Exists fun S : MinimalBoundaryTopologySkeletonFamily.{u} =>
        Nonempty (MinimalBoundaryTopologyMissingLongArcTriangleRunField S) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.nonempty_iff_exists_skeleton_missingField

def minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfLongArcFinitePQSpineCyclicSuccessorRows
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (longArc : MinimalBoundaryTopologyLongArcFieldFamily.{u} S)
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsFamily.{u} S) :
    MinimalBoundaryTopologyMissingLongArcTriangleRunField S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingFieldOfLongArcFinitePQSpineCyclicSuccessorRows
    S longArc H

def minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (longArc : MinimalBoundaryTopologyLongArcFieldFamily.{u} S)
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MinimalBoundaryTopologyMissingLongArcTriangleRunField S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingFieldOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem
    S longArc H

def minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfLongArcTriangleRun
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (longArc : MinimalBoundaryTopologyLongArcFieldFamily.{u} S)
    (triangleRun : MinimalBoundaryTopologyTriangleRunFieldFamily.{u} S) :
    MinimalBoundaryTopologyMissingLongArcTriangleRunField S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingFieldOfLongArcTriangleRun
    S longArc triangleRun

def minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (gapRows : MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u} S)
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MinimalBoundaryTopologyMissingLongArcTriangleRunField S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingFieldOfBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem
    S gapRows H

def minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfTriangleRunBoundaryLongArcGapNegativeRows
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (triangleRun : MinimalBoundaryTopologyTriangleRunFieldFamily.{u} S)
    (gapRows : MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u} S) :
    MinimalBoundaryTopologyMissingLongArcTriangleRunField S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingFieldOfTriangleRunBoundaryLongArcGapNegativeRows
    S triangleRun gapRows

def minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (noGapRows : MinimalBoundaryTopologyNoBoundaryGapTriangleDegree34Rows.{u} S)
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MinimalBoundaryTopologyMissingLongArcTriangleRunField S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingFieldOfNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
    S noGapRows H

def minimalBoundaryTopologyTriangleRunFieldFamilyOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (longArc : MinimalBoundaryTopologyLongArcFieldFamily.{u} S)
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MinimalBoundaryTopologyTriangleRunFieldFamily S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.triangleRunFieldFamilyOfFinitePQSpineCyclicSuccessorRowsTheorem
    S longArc H

noncomputable def minimalBoundaryTopologyTriangleRunFieldFamilyOfBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (gapRows : MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u} S)
    (H : MinimalBoundaryTopologyExplicitM8TriangleRunIndicesTheorem.{u}) :
    MinimalBoundaryTopologyTriangleRunFieldFamily S :=
  BoundaryAngleTurnW11.UDConfigRoute.BoundaryAngleTurnTopologyPackage.MinimalBoundaryTopologyBoundaryTurnAngleRows.triangleRunOfExplicitM8TriangleRunIndicesTheoremAndBoundaryLongArcGapNegativeRows
    (S := S) gapRows H

noncomputable def minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (gapRows : MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u} S)
    (H : MinimalBoundaryTopologyExplicitM8TriangleRunIndicesTheorem.{u}) :
    MinimalBoundaryTopologyMissingLongArcTriangleRunField S :=
  minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfTriangleRunBoundaryLongArcGapNegativeRows
    S
    (minimalBoundaryTopologyTriangleRunFieldFamilyOfBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem
      S gapRows H)
    gapRows

theorem nonempty_minimalBoundaryTopologyTriangleRunFieldFamily_of_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (longArc : MinimalBoundaryTopologyLongArcFieldFamily.{u} S)
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (MinimalBoundaryTopologyTriangleRunFieldFamily S) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.triangleRunFieldFamily_nonempty_of_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    S longArc H

theorem nonempty_minimalBoundaryTopologyMissingLongArcTriangleRunField_of_longArc_finitePQSpineCyclicSuccessorRows
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (longArc : MinimalBoundaryTopologyLongArcFieldFamily.{u} S)
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsFamily.{u} S) :
    Nonempty (MinimalBoundaryTopologyMissingLongArcTriangleRunField S) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingField_nonempty_of_skeleton_longArc_finitePQSpineCyclicSuccessorRows
    S longArc H

theorem nonempty_minimalBoundaryTopologyMissingLongArcTriangleRunField_of_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (longArc : MinimalBoundaryTopologyLongArcFieldFamily.{u} S)
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (MinimalBoundaryTopologyMissingLongArcTriangleRunField S) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingField_nonempty_of_skeleton_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    S longArc H

theorem nonempty_minimalBoundaryTopologyMissingLongArcTriangleRunField_of_longArc_triangleRun
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (longArc : MinimalBoundaryTopologyLongArcFieldFamily.{u} S)
    (triangleRun : MinimalBoundaryTopologyTriangleRunFieldFamily.{u} S) :
    Nonempty (MinimalBoundaryTopologyMissingLongArcTriangleRunField S) :=
  Nonempty.intro
    (minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfLongArcTriangleRun
      S longArc triangleRun)

theorem nonempty_minimalBoundaryTopologyMissingLongArcTriangleRunField_of_boundaryLongArcGapNegativeRows_finitePQSpineCyclicSuccessorRowsTheorem
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (gapRows : MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u} S)
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (MinimalBoundaryTopologyMissingLongArcTriangleRunField S) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingField_nonempty_of_boundaryLongArcGapNegativeRows_finitePQSpineCyclicSuccessorRowsTheorem
    S gapRows H

theorem nonempty_minimalBoundaryTopologyMissingLongArcTriangleRunField_of_triangleRun_boundaryLongArcGapNegativeRows
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (triangleRun : MinimalBoundaryTopologyTriangleRunFieldFamily.{u} S)
    (gapRows : MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u} S) :
    Nonempty (MinimalBoundaryTopologyMissingLongArcTriangleRunField S) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingField_nonempty_of_triangleRun_boundaryLongArcGapNegativeRows
    S triangleRun gapRows

theorem nonempty_minimalBoundaryTopologyMissingLongArcTriangleRunField_of_boundaryLongArcGapNegativeRows_explicitM8TriangleRunIndicesTheorem
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (gapRows : MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u} S)
    (H : MinimalBoundaryTopologyExplicitM8TriangleRunIndicesTheorem.{u}) :
    Nonempty (MinimalBoundaryTopologyMissingLongArcTriangleRunField S) :=
  Nonempty.intro
    (minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem
      S gapRows H)

theorem nonempty_minimalBoundaryTopologyMissingLongArcTriangleRunField_of_noBoundaryGapTriangleDegree34Rows_finitePQSpineCyclicSuccessorRowsTheorem
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (noGapRows : MinimalBoundaryTopologyNoBoundaryGapTriangleDegree34Rows.{u} S)
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (MinimalBoundaryTopologyMissingLongArcTriangleRunField S) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingField_nonempty_of_noBoundaryGapTriangleDegree34Rows_finitePQSpineCyclicSuccessorRowsTheorem
    S noGapRows H

def minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfRemainingActualCycleSkeletonRowsFinitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (rows : RemainingActualCycleSkeletonRemainderRows.{u} h)
    (longArc :
      MinimalBoundaryTopologyLongArcFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MinimalBoundaryTopologyMissingLongArcTriangleRunField
      (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
        h rows) :=
  minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem
    (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
      h rows)
    longArc H

theorem nonempty_minimalBoundaryTopologyMissingLongArcTriangleRunField_of_remainingActualCycleSkeletonRows_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (rows : RemainingActualCycleSkeletonRemainderRows.{u} h)
    (longArc :
      MinimalBoundaryTopologyLongArcFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty
      (MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          h rows)) :=
  nonempty_minimalBoundaryTopologyMissingLongArcTriangleRunField_of_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
      h rows)
    longArc H

theorem minimalBoundaryTopologyWitnessFamily_nonempty_of_skeleton_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    (S : MinimalBoundaryTopologySkeletonFamily.{u})
    (longArc : MinimalBoundaryTopologyLongArcFieldFamily.{u} S)
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty MinimalBoundaryTopologyWitnessFamily.{u} :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.nonempty_of_skeleton_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    S longArc H

def minimalBoundaryTopologySkeletonFamilyOfBoundaryAngleTurnTopologyPackageFamily
    (packages : BoundaryAngleTurnTopologyPackageFamily.{u}) :
    MinimalBoundaryTopologySkeletonFamily.{u} where
  row := fun C hmin =>
    (packages C hmin).toMinimalBoundaryTopologySkeleton hmin

def minimalBoundaryTopologyLongArcFieldFamilyOfBoundaryAngleTurnTopologyPackageFamily
    (packages : BoundaryAngleTurnTopologyPackageFamily.{u}) :
    MinimalBoundaryTopologyLongArcFieldFamily
      (minimalBoundaryTopologySkeletonFamilyOfBoundaryAngleTurnTopologyPackageFamily
        packages) :=
  fun C hmin =>
    (packages C hmin).minimalBoundaryTopologySkeletonLongArc hmin

theorem nonempty_minimalBoundaryTopologyLongArcFieldFamily_of_boundaryAngleTurnTopologyPackageFamily
    (packages : BoundaryAngleTurnTopologyPackageFamily.{u}) :
    Nonempty
      (MinimalBoundaryTopologyLongArcFieldFamily
        (minimalBoundaryTopologySkeletonFamilyOfBoundaryAngleTurnTopologyPackageFamily
          packages)) :=
  Nonempty.intro
    (minimalBoundaryTopologyLongArcFieldFamilyOfBoundaryAngleTurnTopologyPackageFamily
      packages)

abbrev BoundaryAngleTurnTopologyPackageTriangleRunFamily
    (packages : BoundaryAngleTurnTopologyPackageFamily.{u}) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.TriangleRunFieldFamily
    (minimalBoundaryTopologySkeletonFamilyOfBoundaryAngleTurnTopologyPackageFamily
      packages)

def minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfBoundaryAngleTurnTopologyPackageFamily
    (packages : BoundaryAngleTurnTopologyPackageFamily.{u})
    (triangleRun :
      BoundaryAngleTurnTopologyPackageTriangleRunFamily packages) :
    MinimalBoundaryTopologyMissingLongArcTriangleRunField
      (minimalBoundaryTopologySkeletonFamilyOfBoundaryAngleTurnTopologyPackageFamily
        packages) :=
  fun C hmin =>
    (packages C hmin).missingLongArcTriangleRunFieldOfTriangleRun hmin
      (triangleRun C hmin)

def minimalBoundaryTopologyWitnessFamilyOfBoundaryAngleTurnTopologyPackageFamily
    (packages : BoundaryAngleTurnTopologyPackageFamily.{u})
    (triangleRun :
      BoundaryAngleTurnTopologyPackageTriangleRunFamily packages) :
    MinimalBoundaryTopologyWitnessFamily.{u} :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.ofSkeletonAndMissingField
    (minimalBoundaryTopologySkeletonFamilyOfBoundaryAngleTurnTopologyPackageFamily
      packages)
    (minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfBoundaryAngleTurnTopologyPackageFamily
      packages triangleRun)

theorem minimalBoundaryTopologyWitnessFamily_nonempty_of_boundaryAngleTurnTopologyPackageFamily
    (packages : BoundaryAngleTurnTopologyPackageFamily.{u})
    (triangleRun :
      BoundaryAngleTurnTopologyPackageTriangleRunFamily packages) :
    Nonempty MinimalBoundaryTopologyWitnessFamily.{u} :=
  Nonempty.intro
    (minimalBoundaryTopologyWitnessFamilyOfBoundaryAngleTurnTopologyPackageFamily
      packages triangleRun)

def concreteTopologyFactsRowsOfMinimalBoundaryTopologyWitnessFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    MinimalFailureConcreteTopologyFactsRows :=
  fun C hmin => (F.row C hmin).topology

def actualSelectedTopologyRowsOfMinimalBoundaryTopologyWitnessFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    MinimalFailureActualSelectedTopologyRows :=
  actualTopologyRowsOfConcreteTopologyFactsRows
    (concreteTopologyFactsRowsOfMinimalBoundaryTopologyWitnessFamily F)

theorem selectedTopologySourceTarget_of_minimalBoundaryTopologyWitnessFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    MinimalFailureSelectedTopologySourceTarget :=
  minimalFailureSelectedTopologySourceTarget_of_concreteTopologyFactsRows
    (concreteTopologyFactsRowsOfMinimalBoundaryTopologyWitnessFamily F)

theorem selectedTopologySourceTarget_of_nonempty_minimalBoundaryTopologyWitnessFamily
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    MinimalFailureSelectedTopologySourceTarget := by
  cases h with
  | intro F =>
      exact selectedTopologySourceTarget_of_minimalBoundaryTopologyWitnessFamily F

theorem nonempty_actualSelectedTopologyRows_of_minimalBoundaryTopologyWitnessFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty MinimalFailureActualSelectedTopologyRows :=
  Nonempty.intro
    (actualSelectedTopologyRowsOfMinimalBoundaryTopologyWitnessFamily F)

def actualSelectedRemainingWitnessRowsOfMinimalBoundaryTopologyWitnessFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        ActualSelectedRemainingWitnessFields.{u} C hmin
          (actualSelectedTopologyRowsOfMinimalBoundaryTopologyWitnessFamily F
            C hmin) :=
  fun C hmin =>
    let P := F.row C hmin
    { classification := P.classification
      geometricAngleSum := P.geometricAngleSum
      forced_le_geometric := P.forced_le_geometric
      geometric_le_polygon := P.geometric_le_polygon
      Subpolygon := P.Subpolygon
      subpolygonData := P.subpolygonData
      longArc := P.longArc
      triangleRun := P.triangleRun }

def actualSelectedRemainingComponentRowsOfMinimalBoundaryTopologyWitnessFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    ActualTopologyRemainingComponentRows.{u}
      (actualSelectedTopologyRowsOfMinimalBoundaryTopologyWitnessFamily F) :=
  { row := fun C hmin =>
      actualSelectedRemainingComponentFieldsOfWitnessFields
        (C := C) (hmin := hmin)
        (topology :=
          actualSelectedTopologyRowsOfMinimalBoundaryTopologyWitnessFamily F
            C hmin)
        (actualSelectedRemainingWitnessRowsOfMinimalBoundaryTopologyWitnessFamily F
          C hmin) }

def actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    ActualTopologyExtractedComponentClosurePackage.{u} :=
  actualTopologyClosurePackageOfActualTopologyRows
    (actualSelectedTopologyRowsOfMinimalBoundaryTopologyWitnessFamily F)
    (actualSelectedRemainingComponentRowsOfMinimalBoundaryTopologyWitnessFamily F)

def actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (rows : RemainingActualCycleSkeletonRemainderRows.{u} h)
    (missing :
      MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          h rows)) :
    ActualTopologyExtractedComponentClosurePackage.{u} :=
  actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
    (minimalBoundaryTopologyWitnessFamilyOfRemainingActualCycleSkeletonRows
      h rows missing)

def minimalBoundaryTopologyWitnessFamilyOfRemainingActualCycleSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (rows : RemainingActualCycleSkeletonRemainderRows.{u} h)
    (longArc :
      MinimalBoundaryTopologyLongArcFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MinimalBoundaryTopologyWitnessFamily.{u} :=
  minimalBoundaryTopologyWitnessFamilyOfRemainingActualCycleSkeletonRows
    h rows
    (minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfRemainingActualCycleSkeletonRowsFinitePQSpineCyclicSuccessorRowsTheorem
      h rows longArc H)

def actualTopologyClosurePackageOfRemainingActualCycleSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (rows : RemainingActualCycleSkeletonRemainderRows.{u} h)
    (longArc :
      MinimalBoundaryTopologyLongArcFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    ActualTopologyExtractedComponentClosurePackage.{u} :=
  actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
    h rows
    (minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfRemainingActualCycleSkeletonRowsFinitePQSpineCyclicSuccessorRowsTheorem
      h rows longArc H)

def minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (longArc :
      MinimalBoundaryTopologyLongArcFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MinimalBoundaryTopologyMissingLongArcTriangleRunField
      (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
        h rows) :=
  minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfRemainingActualCycleSkeletonRowsFinitePQSpineCyclicSuccessorRowsTheorem
    (remainingActualOuterBoundaryCycleTheoremTargetOfExactActualTopologyFieldsTarget
      h)
    rows longArc H

def minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfExactActualTopologyFieldsTargetSkeletonRowsNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (noGapRows :
      MinimalBoundaryTopologyNoBoundaryGapTriangleDegree34Rows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MinimalBoundaryTopologyMissingLongArcTriangleRunField
      (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
        h rows) :=
  minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
    (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
      h rows)
    noGapRows H

noncomputable def minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfExactActualTopologyFieldsTargetSkeletonRowsBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (gapRows :
      MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyExplicitM8TriangleRunIndicesTheorem.{u}) :
    MinimalBoundaryTopologyMissingLongArcTriangleRunField
      (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
        h rows) :=
  minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem
    (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
      h rows)
    gapRows H

def actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsMissingLongArcTriangleRunField
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (missing :
      MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows)) :
    ActualTopologyExtractedComponentClosurePackage.{u} :=
  actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
    (remainingActualOuterBoundaryCycleTheoremTargetOfExactActualTopologyFieldsTarget
      h)
    rows missing

def actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (longArc :
      MinimalBoundaryTopologyLongArcFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    ActualTopologyExtractedComponentClosurePackage.{u} :=
  actualTopologyClosurePackageOfRemainingActualCycleSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
    (remainingActualOuterBoundaryCycleTheoremTargetOfExactActualTopologyFieldsTarget
      h)
    rows longArc H

def actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (noGapRows :
      MinimalBoundaryTopologyNoBoundaryGapTriangleDegree34Rows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    ActualTopologyExtractedComponentClosurePackage.{u} :=
  actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsMissingLongArcTriangleRunField
    h rows
    (minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfExactActualTopologyFieldsTargetSkeletonRowsNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
      h rows noGapRows H)

noncomputable def actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (gapRows :
      MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyExplicitM8TriangleRunIndicesTheorem.{u}) :
    ActualTopologyExtractedComponentClosurePackage.{u} :=
  actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsMissingLongArcTriangleRunField
    h rows
    (minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfExactActualTopologyFieldsTargetSkeletonRowsBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem
      h rows gapRows H)

abbrev ExactActualTopologyClosureMissingFieldPackage
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h) :=
  Sigma fun missing :
      MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows) =>
    { closure : ActualTopologyExtractedComponentClosurePackage.{u} //
      closure =
        actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
        (remainingActualOuterBoundaryCycleTheoremTargetOfExactActualTopologyFieldsTarget
            h)
          rows missing }

def exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsMissingLongArcTriangleRunField
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (missing :
      MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows)) :
    ExactActualTopologyClosureMissingFieldPackage.{u} h rows :=
  Sigma.mk missing
    (Subtype.mk
      (actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
        (remainingActualOuterBoundaryCycleTheoremTargetOfExactActualTopologyFieldsTarget
          h)
        rows missing)
      rfl)

def exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (longArc :
      MinimalBoundaryTopologyLongArcFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    ExactActualTopologyClosureMissingFieldPackage.{u} h rows :=
  let missing :
      MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows) :=
    minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
      h rows longArc H
  exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsMissingLongArcTriangleRunField
    h rows missing

def exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsLongArcTriangleRun
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (longArc :
      MinimalBoundaryTopologyLongArcFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (triangleRun :
      MinimalBoundaryTopologyTriangleRunFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows)) :
    ExactActualTopologyClosureMissingFieldPackage.{u} h rows :=
  exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsMissingLongArcTriangleRunField
    h rows
    (minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfLongArcTriangleRun
      (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
        h rows)
      longArc triangleRun)

def exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (gapRows :
      MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    ExactActualTopologyClosureMissingFieldPackage.{u} h rows :=
  exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsMissingLongArcTriangleRunField
    h rows
    (minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem
      (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
        h rows)
      gapRows H)

def exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsTriangleRunBoundaryLongArcGapNegativeRows
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (triangleRun :
      MinimalBoundaryTopologyTriangleRunFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (gapRows :
      MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows)) :
    ExactActualTopologyClosureMissingFieldPackage.{u} h rows :=
  exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsMissingLongArcTriangleRunField
    h rows
    (minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfTriangleRunBoundaryLongArcGapNegativeRows
      (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
        h rows)
      triangleRun gapRows)

def exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (noGapRows :
      MinimalBoundaryTopologyNoBoundaryGapTriangleDegree34Rows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    ExactActualTopologyClosureMissingFieldPackage.{u} h rows :=
  exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsMissingLongArcTriangleRunField
    h rows
    (minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
      (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
        h rows)
      noGapRows H)

noncomputable def exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (gapRows :
      MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyExplicitM8TriangleRunIndicesTheorem.{u}) :
    ExactActualTopologyClosureMissingFieldPackage.{u} h rows :=
  exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsMissingLongArcTriangleRunField
    h rows
    (minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfExactActualTopologyFieldsTargetSkeletonRowsBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem
      h rows gapRows H)

theorem nonempty_exactActualTopologyClosureMissingFieldPackage_of_skeletonRows_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (longArc :
      MinimalBoundaryTopologyLongArcFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (ExactActualTopologyClosureMissingFieldPackage.{u} h rows) :=
  Nonempty.intro
    (exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
      h rows longArc H)

theorem nonempty_exactActualTopologyClosureMissingFieldPackage_of_skeletonRows_missingLongArcTriangleRunField
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (missing :
      MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows)) :
    Nonempty (ExactActualTopologyClosureMissingFieldPackage.{u} h rows) :=
  Nonempty.intro
    (exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsMissingLongArcTriangleRunField
      h rows missing)

theorem nonempty_exactActualTopologyClosureMissingFieldPackage_of_skeletonRows_longArc_triangleRun
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (longArc :
      MinimalBoundaryTopologyLongArcFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (triangleRun :
      MinimalBoundaryTopologyTriangleRunFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows)) :
    Nonempty (ExactActualTopologyClosureMissingFieldPackage.{u} h rows) :=
  Nonempty.intro
    (exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsLongArcTriangleRun
      h rows longArc triangleRun)

theorem nonempty_exactActualTopologyClosureMissingFieldPackage_of_skeletonRows_boundaryLongArcGapNegativeRows_finitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (gapRows :
      MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (ExactActualTopologyClosureMissingFieldPackage.{u} h rows) :=
  Nonempty.intro
    (exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem
      h rows gapRows H)

theorem nonempty_exactActualTopologyClosureMissingFieldPackage_of_skeletonRows_triangleRun_boundaryLongArcGapNegativeRows
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (triangleRun :
      MinimalBoundaryTopologyTriangleRunFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (gapRows :
      MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows)) :
    Nonempty (ExactActualTopologyClosureMissingFieldPackage.{u} h rows) :=
  Nonempty.intro
    (exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsTriangleRunBoundaryLongArcGapNegativeRows
      h rows triangleRun gapRows)

theorem nonempty_exactActualTopologyClosureMissingFieldPackage_of_skeletonRows_noBoundaryGapTriangleDegree34Rows_finitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (noGapRows :
      MinimalBoundaryTopologyNoBoundaryGapTriangleDegree34Rows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (ExactActualTopologyClosureMissingFieldPackage.{u} h rows) :=
  Nonempty.intro
    (exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
      h rows noGapRows H)

theorem nonempty_exactActualTopologyClosureMissingFieldPackage_of_skeletonRows_boundaryLongArcGapNegativeRows_explicitM8TriangleRunIndicesTheorem
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (gapRows :
      MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyExplicitM8TriangleRunIndicesTheorem.{u}) :
    Nonempty (ExactActualTopologyClosureMissingFieldPackage.{u} h rows) :=
  Nonempty.intro
    (exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem
      h rows gapRows H)

def missingLongArcTriangleRunFieldOfExactActualTopologyClosureMissingFieldPackage
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (P : ExactActualTopologyClosureMissingFieldPackage.{u} h rows) :
    MinimalBoundaryTopologyMissingLongArcTriangleRunField
      (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
        h rows) :=
  P.1

def actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (P : ExactActualTopologyClosureMissingFieldPackage.{u} h rows) :
    ActualTopologyExtractedComponentClosurePackage.{u} :=
  P.2.1

theorem actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage_eq
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (P : ExactActualTopologyClosureMissingFieldPackage.{u} h rows) :
    actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
        h rows P =
      actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
        (remainingActualOuterBoundaryCycleTheoremTargetOfExactActualTopologyFieldsTarget
          h)
        rows
        (missingLongArcTriangleRunFieldOfExactActualTopologyClosureMissingFieldPackage
          h rows P) :=
  P.2.2

theorem actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackageOfSkeletonRowsMissingLongArcTriangleRunField_eq
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (missing :
      MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows)) :
    actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsMissingLongArcTriangleRunField
        h rows missing =
      actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
        h rows
        (exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsMissingLongArcTriangleRunField
          h rows missing) :=
  rfl

theorem actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackageOfSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem_eq
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (longArc :
      MinimalBoundaryTopologyLongArcFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
        h rows longArc H =
      actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
        h rows
        (exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
          h rows longArc H) :=
  rfl

theorem actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackageOfSkeletonRowsNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem_eq
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (noGapRows :
      MinimalBoundaryTopologyNoBoundaryGapTriangleDegree34Rows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
        h rows noGapRows H =
      actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
        h rows
        (exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
          h rows noGapRows H) :=
  rfl

theorem actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackageOfSkeletonRowsBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem_eq
    (h : MinimalFailureExactActualTopologyFieldsTarget)
    (rows : ExactActualTopologySkeletonRemainderRows.{u} h)
    (gapRows :
      MinimalBoundaryTopologyBoundaryLongArcGapNegativeRows.{u}
        (minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          h rows))
    (H : MinimalBoundaryTopologyExplicitM8TriangleRunIndicesTheorem.{u}) :
    actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem
        h rows gapRows H =
      actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
        h rows
        (exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem
          h rows gapRows H) :=
  rfl

theorem actualTopologyClosurePackage_nonempty_of_remainingActualCycleSkeletonRows
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (rows : RemainingActualCycleSkeletonRemainderRows.{u} h)
    (missing :
      MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          h rows)) :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} :=
  Nonempty.intro
    (actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
      h rows missing)

theorem actualTopologyClosurePackage_nonempty_of_remainingActualCycleSkeletonRows_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (rows : RemainingActualCycleSkeletonRemainderRows.{u} h)
    (longArc :
      MinimalBoundaryTopologyLongArcFieldFamily.{u}
        (minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          h rows))
    (H : MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} :=
  Nonempty.intro
    (actualTopologyClosurePackageOfRemainingActualCycleSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
      h rows longArc H)

def minimalBoundaryTopologyWitnessFamilyOfActualTopologyClosurePackage
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    MinimalBoundaryTopologyWitnessFamily.{u} :=
  P.toSelectedFaceWitnessFamily.toW24WitnessFamily

theorem actualTopologyClosurePackage_nonempty_of_minimalBoundaryTopologyWitnessFamily
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} := by
  cases h with
  | intro F =>
      exact
        Nonempty.intro
          (actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily F)

theorem minimalBoundaryTopologyWitnessFamily_nonempty_of_actualTopologyClosurePackage
    (h : Nonempty ActualTopologyExtractedComponentClosurePackage.{u}) :
    Nonempty MinimalBoundaryTopologyWitnessFamily.{u} := by
  cases h with
  | intro P =>
      exact
        Nonempty.intro
          (minimalBoundaryTopologyWitnessFamilyOfActualTopologyClosurePackage P)

theorem actualTopologyClosurePackage_nonempty_iff_minimalBoundaryTopologyWitnessFamily :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} <->
      Nonempty MinimalBoundaryTopologyWitnessFamily.{u} := by
  constructor
  case mp =>
    exact minimalBoundaryTopologyWitnessFamily_nonempty_of_actualTopologyClosurePackage
  case mpr =>
    exact actualTopologyClosurePackage_nonempty_of_minimalBoundaryTopologyWitnessFamily

def concreteTopologyFactsRowsOfSelectedTopologySourceTarget
    (source : MinimalFailureSelectedTopologySourceTarget) :
    MinimalFailureConcreteTopologyFactsRows := by
  intro n C hmin
  exact
    Classical.choice
      ((MinimalFailureSelectedTopologySourceW32.minimalFailureSelectedTopologySource_iff_concreteTopologyFacts
          hmin).1
        (source C hmin))

def missingTopologyFactsRowsOfSelectedTopologySourceTarget
    (source : MinimalFailureSelectedTopologySourceTarget) :
    MinimalFailureMissingTopologyFactsRows := by
  intro n C hmin
  exact
    Classical.choice
      ((MinimalFailureSelectedTopologySourceW32.route_nonempty_iff_missingTopologyFacts
          C).1
        (source C hmin).route)

def topologyBoundaryRowsOfSelectedTopologySourceTarget
    (source : MinimalFailureSelectedTopologySourceTarget) :
    MinimalFailureTopologyBoundaryRows := by
  intro n C hmin
  exact
    Classical.choice
      ((MinimalFailureSelectedTopologySourceW32.minimalFailureSelectedTopologySource_iff_outerBoundaryCore
          hmin).1
        (source C hmin))

def actualSelectedTopologyRowsOfConcreteTopologySourceTarget
    (source : MinimalFailureSelectedTopologySourceTarget) :
    MinimalFailureActualSelectedTopologyRows :=
  actualTopologyRowsOfConcreteTopologyFactsRows
    (concreteTopologyFactsRowsOfSelectedTopologySourceTarget source)

def actualSelectedTopologyRowsOfMissingTopologySourceTarget
    (source : MinimalFailureSelectedTopologySourceTarget) :
    MinimalFailureActualSelectedTopologyRows :=
  actualTopologyRowsOfMissingTopologyFactsRows
    (missingTopologyFactsRowsOfSelectedTopologySourceTarget source)

def actualSelectedTopologyRowsOfTopologyBoundarySourceTarget
    (source : MinimalFailureSelectedTopologySourceTarget) :
    MinimalFailureActualSelectedTopologyRows :=
  actualTopologyRowsOfTopologyBoundaryRows
    (topologyBoundaryRowsOfSelectedTopologySourceTarget source)

theorem nonempty_actualSelectedTopologyRows_of_selectedTopologySourceTarget
    (source : MinimalFailureSelectedTopologySourceTarget) :
    Nonempty MinimalFailureActualSelectedTopologyRows :=
  Nonempty.intro
    (actualSelectedTopologyRowsOfConcreteTopologySourceTarget source)

theorem selectedTopologySourceTarget_iff_nonempty_concreteTopologyFactsRows :
    MinimalFailureSelectedTopologySourceTarget <->
      Nonempty MinimalFailureConcreteTopologyFactsRows := by
  constructor
  case mp =>
    intro source
    exact
      Nonempty.intro
        (concreteTopologyFactsRowsOfSelectedTopologySourceTarget source)
  case mpr =>
    intro hrows
    cases hrows with
    | intro rows =>
        exact
          minimalFailureSelectedTopologySourceTarget_of_concreteTopologyFactsRows
            rows

theorem selectedTopologySourceTarget_iff_nonempty_missingTopologyFactsRows :
    MinimalFailureSelectedTopologySourceTarget <->
      Nonempty MinimalFailureMissingTopologyFactsRows := by
  constructor
  case mp =>
    intro source
    exact
      Nonempty.intro
        (missingTopologyFactsRowsOfSelectedTopologySourceTarget source)
  case mpr =>
    intro hrows
    cases hrows with
    | intro rows =>
        exact
          minimalFailureSelectedTopologySourceTarget_of_missingTopologyFactsRows
            rows

theorem selectedTopologySourceTarget_iff_nonempty_topologyBoundaryRows :
    MinimalFailureSelectedTopologySourceTarget <->
      Nonempty MinimalFailureTopologyBoundaryRows := by
  constructor
  case mp =>
    intro source
    exact
      Nonempty.intro
        (topologyBoundaryRowsOfSelectedTopologySourceTarget source)
  case mpr =>
    intro hrows
    cases hrows with
    | intro rows =>
        exact
          minimalFailureSelectedTopologySourceTarget_of_topologyBoundaryRows
            rows

abbrev MinimalFailureMissingOuterFaceDataRows : Type 1 :=
  MinimalFailureSelectedTopologySourceW32.MinimalFailureMissingOuterFaceDataRows

def missingOuterFaceDataRowsOfMinimalClearedFailure :
    MinimalFailureMissingOuterFaceDataRows := by
  intro n C hmin
  exact
    Classical.choice
      (JordanBoundaryConcrete.MissingOuterFaceData.nonempty_of_minimalClearedFailure
        (C := C) hmin)

def topologySourceFieldsRowsOfMinimalClearedFailure :
    forall {n : Nat} (C : _root_.UDConfig n),
      MinimalGraphFacts.IsMinimalClearedFailure C ->
        FaceBoundaryTopologySourceW32.TopologySourceFields C := by
  intro n C hmin
  let D :=
    Classical.choice
      (JordanBoundaryConcrete.MissingOuterFaceData.nonempty_of_minimalClearedFailure
        (C := C) hmin)
  exact
    { faceBoundary := D.faceBoundary
      outerFace := D.outerFace
      outerFace_isOuter := D.outerFace_isOuter }

theorem selectedTopologySourceTarget_of_minimalFailureMissingOuterFaceDataTarget :
    MinimalFailureSelectedTopologySourceTarget :=
  MinimalFailureSelectedTopologySourceW32.minimalFailureSelectedTopologySourceTarget_iff_concreteTopologyFactsTarget.2
    (MinimalFailureSelectedTopologySourceW32.concreteTopologyFactsTarget_of_missingOuterFaceDataTarget
      MinimalFailureSelectedTopologySourceW32.minimalFailureMissingOuterFaceDataTarget)

def actualSelectedTopologyRowsOfClosedSelectedTopology :
    MinimalFailureActualSelectedTopologyRows :=
  actualTopologyRowsOfMinimalFailureSelectedTopologySourceTarget
    selectedTopologySourceTarget_of_minimalFailureMissingOuterFaceDataTarget

def actualSelectedTopologyRowsOfClosedTopologySourceFields :
    MinimalFailureActualSelectedTopologyRows :=
  actualSelectedTopologyRowsOfClosedSelectedTopology

def actualTopologyClosurePackageOfClosedSelectedTopology
    (components :
      ActualTopologyRemainingComponentRows.{u}
        actualSelectedTopologyRowsOfClosedSelectedTopology) :
    ActualTopologyExtractedComponentClosurePackage.{u} :=
  actualTopologyClosurePackageOfActualTopologyRows
    actualSelectedTopologyRowsOfClosedSelectedTopology components

theorem actualTopologyClosurePackage_nonempty_of_closedSelectedTopology_components
    (components :
      ActualTopologyRemainingComponentRows.{u}
        actualSelectedTopologyRowsOfClosedSelectedTopology) :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} :=
  Nonempty.intro
    (actualTopologyClosurePackageOfClosedSelectedTopology components)

end

end SelectedTopologyRowsInhabitationW33
end Swanepoel

namespace Verified

universe u

open Swanepoel.SelectedTopologyRowsInhabitationW33
open Swanepoel.ExtractedComponentsConcreteClosureW32

abbrev SwanepoelW33MinimalFailureSelectedTopologySourceTarget : Prop :=
  _root_.ErdosProblems1066.Swanepoel.SelectedTopologyRowsInhabitationW33.MinimalFailureSelectedTopologySourceTarget

theorem swanepoelW33_selectedTopologySource_exactly_concreteTopologyFactsRows :
    SwanepoelW33MinimalFailureSelectedTopologySourceTarget <->
      Nonempty MinimalFailureConcreteTopologyFactsRows :=
  selectedTopologySourceTarget_iff_nonempty_concreteTopologyFactsRows

theorem swanepoelW33_selectedTopologySource_exactly_missingTopologyFactsRows :
    SwanepoelW33MinimalFailureSelectedTopologySourceTarget <->
      Nonempty MinimalFailureMissingTopologyFactsRows :=
  selectedTopologySourceTarget_iff_nonempty_missingTopologyFactsRows

theorem swanepoelW33_selectedTopologySource_exactly_topologyBoundaryRows :
    SwanepoelW33MinimalFailureSelectedTopologySourceTarget <->
      Nonempty MinimalFailureTopologyBoundaryRows :=
  selectedTopologySourceTarget_iff_nonempty_topologyBoundaryRows

theorem swanepoelW33_actualTopologyClosure_exactly_minimalBoundaryTopologyWitnessFamily :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} <->
      Nonempty MinimalBoundaryTopologyWitnessFamily.{u} :=
  actualTopologyClosurePackage_nonempty_iff_minimalBoundaryTopologyWitnessFamily

end Verified
end ErdosProblems1066
