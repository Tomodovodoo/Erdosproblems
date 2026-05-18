import ErdosProblems1066.Swanepoel.ActualTopologyArcInputsProducerW18

set_option autoImplicit false

/-!
# W19 topology arc closure

This file isolates the weakest currently visible source package for producing
`ActualTopologyArcInputs` on a minimal failure.  The older W14-W17 layers reduce
the arc construction to topology, angle/subpolygon/long-arc data, and a
thirteen-edge triangular boundary run.  Once those fields are supplied, the W18
producer gives the actual topology-arc inputs.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyArcClosureW19

open BoundaryArcFiniteWalkConstructionW16
open ExactOuterBoundaryTopologyW13
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  ActualTopologyArcInputsProducerW18.CanonicalGraph C

abbrev ActualTopologyArcInputs (C : _root_.UDConfig n) :=
  ActualTopologyArcInputsProducerW18.ActualTopologyArcInputs.{u} C

abbrev W18ConcreteBudgetSource
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  ActualTopologyArcInputsProducerW18.MinimalFailureConcreteBudgetTriangleSourceFields.{u}
    C hmin

abbrev W18TopologyArcSourceFamily : Type (u + 1) :=
  ActualTopologyArcInputsProducerW18.MinimalFailureActualTopologyArcSourceFamily.{u}

/--
The exact remaining source fields for a topology-arc input on a minimal
failure.  The minimality proof is a phantom parameter: the current constructive
content is the topology/angle/subpolygon/long-arc row plus the triangular
boundary run over the same planar boundary.
-/
structure MinimalFailureTopologyArcSourceFields
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  topology : TopologyFacts C
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)
  longArc :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)
  triangleRun :
    BoundaryArcTriangleRun
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)

namespace MinimalFailureTopologyArcSourceFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def planarBoundary
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  P.topology.toPlanarBoundaryData P.outerAngleBounds P.Subpolygon
    P.subpolygonData

def toTopologyTriangleSourceFields
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    TopologyTrianglePipelineW17.TopologyTriangleSourceFields.{u} C where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

def toConcreteBudgetTriangleSourceFields
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    ActualTopologyArcInputsProducerW18.ConcreteBudgetTriangleSourceFields.{u}
      C where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

def toW18MinimalFailureTriangleSourceFields
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    ActualTopologyArcInputsProducerW18.MinimalFailureTriangleSourceFields.{u}
      C hmin where
  source := P.toTopologyTriangleSourceFields

def toW18MinimalFailureConcreteBudgetTriangleSourceFields
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    W18ConcreteBudgetSource.{u} C hmin where
  source := P.toConcreteBudgetTriangleSourceFields

def toActualTopologyArcInputs
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    ActualTopologyArcInputs.{u} C :=
  P.toW18MinimalFailureConcreteBudgetTriangleSourceFields
    |>.toActualTopologyArcInputs

def finiteWalk
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    BoundaryArcExtractionProofW15.BoundaryArcFiniteWalkData
      P.toActualTopologyArcInputs.planarBoundary :=
  P.triangleRun.toFiniteWalkData

theorem nonempty_actualTopologyArcInputs
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    Nonempty (ActualTopologyArcInputs.{u} C) :=
  Nonempty.intro P.toActualTopologyArcInputs

@[simp]
theorem toTopologyTriangleSourceFields_planarBoundary
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    P.toTopologyTriangleSourceFields.planarBoundary = P.planarBoundary :=
  rfl

@[simp]
theorem toConcreteBudgetTriangleSourceFields_planarBoundary
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    P.toConcreteBudgetTriangleSourceFields.planarBoundary = P.planarBoundary :=
  rfl

@[simp]
theorem toActualTopologyArcInputs_boundaryArc
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    P.toActualTopologyArcInputs.boundaryArc =
      P.triangleRun.toFiniteWalkData.toBoundaryArcCertificate :=
  rfl

@[simp]
theorem finiteWalk_boundaryArc
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    P.toActualTopologyArcInputs.boundaryArc =
      P.finiteWalk.toBoundaryArcCertificate :=
  rfl

end MinimalFailureTopologyArcSourceFields

/-- Output family: an actual topology-arc input for every minimal failure. -/
structure MinimalFailureActualTopologyArcInputsFamily : Type (u + 1) where
  inputs :
    forall {n : Nat} (C : _root_.UDConfig n)
      (_hmin : IsMinimalClearedFailure C),
        ActualTopologyArcInputs.{u} C

namespace MinimalFailureActualTopologyArcInputsFamily

def inputsFor
    (F : MinimalFailureActualTopologyArcInputsFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    ActualTopologyArcInputs.{u} C :=
  F.inputs C hmin

theorem nonempty_inputsFor
    (F : MinimalFailureActualTopologyArcInputsFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    Nonempty (ActualTopologyArcInputs.{u} C) :=
  Nonempty.intro (F.inputsFor C hmin)

end MinimalFailureActualTopologyArcInputsFamily

/--
Source family form of the remaining W19 obligation.  Each row is the exact
topology/angle/subpolygon/long-arc plus triangle-run data needed by W18.
-/
structure MinimalFailureTopologyArcSourceFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureTopologyArcSourceFields.{u} C hmin

namespace MinimalFailureTopologyArcSourceFamily

def toW18SourceFamily
    (F : MinimalFailureTopologyArcSourceFamily.{u}) :
    W18TopologyArcSourceFamily.{u} where
  inputs := fun C hmin =>
    (F.row C hmin).toW18MinimalFailureConcreteBudgetTriangleSourceFields

def toActualTopologyArcInputsFamily
    (F : MinimalFailureTopologyArcSourceFamily.{u}) :
    MinimalFailureActualTopologyArcInputsFamily.{u} where
  inputs := fun C hmin => (F.row C hmin).toActualTopologyArcInputs

def inputsFor
    (F : MinimalFailureTopologyArcSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    ActualTopologyArcInputs.{u} C :=
  (F.row C hmin).toActualTopologyArcInputs

theorem nonempty_inputsFor
    (F : MinimalFailureTopologyArcSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    Nonempty (ActualTopologyArcInputs.{u} C) :=
  Nonempty.intro (F.inputsFor C hmin)

theorem nonempty_actualTopologyArcInputsFamily
    (F : MinimalFailureTopologyArcSourceFamily.{u}) :
    Nonempty MinimalFailureActualTopologyArcInputsFamily.{u} :=
  Nonempty.intro F.toActualTopologyArcInputsFamily

@[simp]
theorem toActualTopologyArcInputsFamily_inputs
    (F : MinimalFailureTopologyArcSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    F.toActualTopologyArcInputsFamily.inputs C hmin =
      (F.row C hmin).toActualTopologyArcInputs :=
  rfl

@[simp]
theorem toW18SourceFamily_inputs
    (F : MinimalFailureTopologyArcSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (F.toW18SourceFamily.inputs C hmin).toActualTopologyArcInputs =
      (F.row C hmin).toActualTopologyArcInputs :=
  rfl

end MinimalFailureTopologyArcSourceFamily

def actualTopologyArcInputsFamilyOfW18SourceFamily
    (F : W18TopologyArcSourceFamily.{u}) :
    MinimalFailureActualTopologyArcInputsFamily.{u} where
  inputs := fun C hmin => F.inputsFor C hmin

theorem actualTopologyArcInputsFamily_nonempty_ofW18SourceFamily
    (F : W18TopologyArcSourceFamily.{u}) :
    Nonempty MinimalFailureActualTopologyArcInputsFamily.{u} :=
  Nonempty.intro (actualTopologyArcInputsFamilyOfW18SourceFamily F)

end

end TopologyArcClosureW19
end Swanepoel
end ErdosProblems1066
