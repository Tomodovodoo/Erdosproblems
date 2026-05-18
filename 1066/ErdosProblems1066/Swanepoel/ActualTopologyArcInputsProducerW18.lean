import ErdosProblems1066.Swanepoel.BoundaryTopologyArcBridgeW16
import ErdosProblems1066.Swanepoel.TopologyTrianglePipelineW17
import ErdosProblems1066.Swanepoel.TriangleRunSelectorW17
import ErdosProblems1066.Swanepoel.BoundaryBudgetLongArcConcreteW17

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace ActualTopologyArcInputsProducerW18

open BoundaryBudgetLongArcConcreteW17
open BoundaryTopologyArcBridgeW16
open BoundaryArcFiniteWalkConstructionW16
open BoundaryArcW12
open ExactOuterBoundaryTopologyW13
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts
open TopologyTrianglePipelineW17

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  ExactOuterBoundaryTopologyW13.CanonicalGraph C

abbrev ActualTopologyArcInputs (C : _root_.UDConfig n) :=
  BoundaryTopologyArcBridgeW16.ActualTopologyArcInputs.{u} C

def ofTriangleSource
    {C : _root_.UDConfig n}
    (S : TopologyTriangleSourceFields.{u} C) :
    ActualTopologyArcInputs.{u} C :=
  S.toTopologyArcFields

def ofFiniteWalkSource
    {C : _root_.UDConfig n}
    (S : TopologyFiniteWalkSourceFields.{u} C) :
    ActualTopologyArcInputs.{u} C :=
  S.toTopologyArcFields

@[simp]
theorem ofTriangleSource_boundaryArc
    {C : _root_.UDConfig n}
    (S : TopologyTriangleSourceFields.{u} C) :
    (ofTriangleSource S).boundaryArc =
      S.finiteWalkData.toBoundaryArcCertificate :=
  rfl

@[simp]
theorem ofFiniteWalkSource_boundaryArc
    {C : _root_.UDConfig n}
    (S : TopologyFiniteWalkSourceFields.{u} C) :
    (ofFiniteWalkSource S).boundaryArc =
      S.finiteWalk.toBoundaryArcCertificate :=
  rfl

def triangleRunOfProduced
    {C : _root_.UDConfig n}
    (S : TopologyTriangleSourceFields.{u} C) :
    BoundaryArcTriangleRun (ofTriangleSource S).planarBoundary :=
  TriangleRunSelectorW17.TopologyBoundaryArcFields.triangleRun
    (ofTriangleSource S)

@[simp]
theorem triangleRunOfProduced_pIndex
    {C : _root_.UDConfig n}
    (S : TopologyTriangleSourceFields.{u} C)
    (i : M8BoundaryIndex) :
    (triangleRunOfProduced S).pIndex i =
      (ofTriangleSource S).boundaryArc.pIndex i :=
  rfl

structure MinimalFailureTriangleSourceFields
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  source : TopologyTriangleSourceFields.{u} C

namespace MinimalFailureTriangleSourceFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def toActualTopologyArcInputs
    (P : MinimalFailureTriangleSourceFields.{u} C hmin) :
    ActualTopologyArcInputs.{u} C :=
  ofTriangleSource P.source

def finiteWalk
    (P : MinimalFailureTriangleSourceFields.{u} C hmin) :
    BoundaryArcExtractionProofW15.BoundaryArcFiniteWalkData
      P.toActualTopologyArcInputs.planarBoundary :=
  P.source.finiteWalkData

theorem nonempty_actualTopologyArcInputs
    (P : MinimalFailureTriangleSourceFields.{u} C hmin) :
    Nonempty (ActualTopologyArcInputs.{u} C) :=
  Nonempty.intro P.toActualTopologyArcInputs

@[simp]
theorem toActualTopologyArcInputs_boundaryArc
    (P : MinimalFailureTriangleSourceFields.{u} C hmin) :
    P.toActualTopologyArcInputs.boundaryArc =
      P.finiteWalk.toBoundaryArcCertificate :=
  rfl

end MinimalFailureTriangleSourceFields

structure MinimalFailureFiniteWalkSourceFields
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  source : TopologyFiniteWalkSourceFields.{u} C

namespace MinimalFailureFiniteWalkSourceFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def toActualTopologyArcInputs
    (P : MinimalFailureFiniteWalkSourceFields.{u} C hmin) :
    ActualTopologyArcInputs.{u} C :=
  ofFiniteWalkSource P.source

theorem nonempty_actualTopologyArcInputs
    (P : MinimalFailureFiniteWalkSourceFields.{u} C hmin) :
    Nonempty (ActualTopologyArcInputs.{u} C) :=
  Nonempty.intro P.toActualTopologyArcInputs

@[simp]
theorem toActualTopologyArcInputs_boundaryArc
    (P : MinimalFailureFiniteWalkSourceFields.{u} C hmin) :
    P.toActualTopologyArcInputs.boundaryArc =
      P.source.finiteWalk.toBoundaryArcCertificate :=
  rfl

end MinimalFailureFiniteWalkSourceFields

structure ConcreteBudgetTriangleSourceFields
    (C : _root_.UDConfig n) where
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

namespace ConcreteBudgetTriangleSourceFields

variable {C : _root_.UDConfig n}

def planarBoundary
    (P : ConcreteBudgetTriangleSourceFields.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  P.topology.toPlanarBoundaryData P.outerAngleBounds P.Subpolygon
    P.subpolygonData

def toTopologyTriangleSourceFields
    (P : ConcreteBudgetTriangleSourceFields.{u} C) :
    TopologyTriangleSourceFields.{u} C where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

def toActualTopologyArcInputs
    (P : ConcreteBudgetTriangleSourceFields.{u} C) :
    ActualTopologyArcInputs.{u} C :=
  ofTriangleSource P.toTopologyTriangleSourceFields

def boundaryLongArcFacts
    (P : ConcreteBudgetTriangleSourceFields.{u} C) :
    NonconcaveArcBudgetFromBoundary.BoundaryLongArcFacts P.planarBoundary :=
  P.longArc.toBoundaryLongArcFacts

def selectedBudget
    (P : ConcreteBudgetTriangleSourceFields.{u} C) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u}
      (CanonicalGraph C) :=
  P.longArc.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem toTopologyTriangleSourceFields_planarBoundary
    (P : ConcreteBudgetTriangleSourceFields.{u} C) :
    P.toTopologyTriangleSourceFields.planarBoundary = P.planarBoundary :=
  rfl

@[simp]
theorem toActualTopologyArcInputs_boundaryArc
    (P : ConcreteBudgetTriangleSourceFields.{u} C) :
    P.toActualTopologyArcInputs.boundaryArc =
      P.triangleRun.toFiniteWalkData.toBoundaryArcCertificate :=
  rfl

@[simp]
theorem selectedBudget_planarBoundary
    (P : ConcreteBudgetTriangleSourceFields.{u} C) :
    P.selectedBudget.planarBoundary = P.planarBoundary :=
  rfl

end ConcreteBudgetTriangleSourceFields

structure MinimalFailureConcreteBudgetTriangleSourceFields
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  source : ConcreteBudgetTriangleSourceFields.{u} C

namespace MinimalFailureConcreteBudgetTriangleSourceFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def toActualTopologyArcInputs
    (P : MinimalFailureConcreteBudgetTriangleSourceFields.{u} C hmin) :
    ActualTopologyArcInputs.{u} C :=
  P.source.toActualTopologyArcInputs

theorem nonempty_actualTopologyArcInputs
    (P : MinimalFailureConcreteBudgetTriangleSourceFields.{u} C hmin) :
    Nonempty (ActualTopologyArcInputs.{u} C) :=
  Nonempty.intro P.toActualTopologyArcInputs

end MinimalFailureConcreteBudgetTriangleSourceFields

structure ConcreteLemma67BudgetFields
    {C : _root_.UDConfig n}
    {core : OuterBoundaryCore (CanonicalGraph C)}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C))
    where
  lemma67 :
    Lemma67ToBoundaryArcW14.Lemma67BoundaryArcInput C
      (OuterAngleBudgetProofW15.ActualPlanarBoundary
        (OuterAngleBudgetProofW15.actualAngleDataOfConcreteWitnesses
          classification angleWitness)
        Subpolygon subpolygonData)

namespace ConcreteLemma67BudgetFields

variable {C : _root_.UDConfig n}
variable {core : OuterBoundaryCore (CanonicalGraph C)}
variable
  {classification :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      core}
variable
  {angleWitness :
    OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification}
variable {Subpolygon : Type u}
variable
  {subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}

def actualWitness
    (P :
      ConcreteLemma67BudgetFields.{u}
        classification angleWitness Subpolygon subpolygonData) :
    OuterAngleBudgetProofW15.ActualOuterAngleBudgetWitness.{u}
      (CanonicalGraph C) :=
  actualWitnessOfConcreteAnglesAndLemma67
    classification angleWitness Subpolygon subpolygonData P.lemma67

def actualBudgetFields
    (P :
      ConcreteLemma67BudgetFields.{u}
        classification angleWitness Subpolygon subpolygonData) :
    BoundaryAnglesToBudgetW14.ActualOuterBoundaryAngleBudgetFields
      (OuterAngleBudgetProofW15.actualAngleDataOfConcreteWitnesses
        classification angleWitness)
      Subpolygon subpolygonData
      (P.lemma67.boundaryLongArcExistenceFields.rawTurn
        P.lemma67.boundaryLongArcExistenceFields.selectedLongArc) :=
  actualBudgetFieldsOfConcreteAnglesAndLemma67
    classification angleWitness Subpolygon subpolygonData P.lemma67

def boundaryArcInstantiation
    (P :
      ConcreteLemma67BudgetFields.{u}
        classification angleWitness Subpolygon subpolygonData) :
    BoundaryArcInstantiationW13.BoundaryArcInstantiation
      (OuterAngleBudgetProofW15.ActualPlanarBoundary
        (OuterAngleBudgetProofW15.actualAngleDataOfConcreteWitnesses
          classification angleWitness)
        Subpolygon subpolygonData) :=
  boundaryArcInstantiationOfConcreteAnglesAndLemma67
    classification angleWitness Subpolygon subpolygonData P.lemma67

theorem actualBudgetFields_lt_pi_div_three
    (P :
      ConcreteLemma67BudgetFields.{u}
        classification angleWitness Subpolygon subpolygonData) :
    P.actualBudgetFields.geometricAngleBudget < Real.pi / 3 :=
  actualBudgetFieldsOfConcreteAnglesAndLemma67_lt_pi_div_three
    classification angleWitness Subpolygon subpolygonData P.lemma67

@[simp]
theorem boundaryArcInstantiation_boundaryArc
    (P :
      ConcreteLemma67BudgetFields.{u}
        classification angleWitness Subpolygon subpolygonData) :
    P.boundaryArcInstantiation.boundaryArc = P.lemma67.boundaryArc :=
  rfl

end ConcreteLemma67BudgetFields

structure ConcreteTopologyLemma67TriangleSourceFields
    (C : _root_.UDConfig n) where
  topology : TopologyFacts C
  classification :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      topology.toCore
  angleWitness :
    OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)
  lemma67 :
    Lemma67ToBoundaryArcW14.Lemma67BoundaryArcInput C
      (OuterAngleBudgetProofW15.ActualPlanarBoundary
        (OuterAngleBudgetProofW15.actualAngleDataOfConcreteWitnesses
          classification angleWitness)
        Subpolygon subpolygonData)
  triangleRun :
    BoundaryArcTriangleRun
      (topology.toPlanarBoundaryData
        ((BoundaryAnglesToBudgetW14.actualToExplicitAngleFields
          (OuterAngleBudgetProofW15.actualAngleDataOfConcreteWitnesses
            classification angleWitness)).angleBounds)
        Subpolygon subpolygonData)

namespace ConcreteTopologyLemma67TriangleSourceFields

variable {C : _root_.UDConfig n}

def angleData
    (P : ConcreteTopologyLemma67TriangleSourceFields.{u} C) :
    OuterBoundaryInstantiationW13.ActualOuterBoundaryAngleData
      (CanonicalGraph C) :=
  OuterAngleBudgetProofW15.actualAngleDataOfConcreteWitnesses
    P.classification P.angleWitness

def outerAngleBounds
    (P : ConcreteTopologyLemma67TriangleSourceFields.{u} C) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} :=
  (BoundaryAnglesToBudgetW14.actualToExplicitAngleFields P.angleData).angleBounds

def planarBoundary
    (P : ConcreteTopologyLemma67TriangleSourceFields.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  P.topology.toPlanarBoundaryData P.outerAngleBounds P.Subpolygon
    P.subpolygonData

def actualWitness
    (P : ConcreteTopologyLemma67TriangleSourceFields.{u} C) :
    OuterAngleBudgetProofW15.ActualOuterAngleBudgetWitness.{u}
      (CanonicalGraph C) :=
  actualWitnessOfConcreteAnglesAndLemma67
    P.classification P.angleWitness P.Subpolygon P.subpolygonData
    P.lemma67

def actualBudgetFields
    (P : ConcreteTopologyLemma67TriangleSourceFields.{u} C) :
    BoundaryAnglesToBudgetW14.ActualOuterBoundaryAngleBudgetFields
      P.angleData P.Subpolygon P.subpolygonData
      (P.lemma67.boundaryLongArcExistenceFields.rawTurn
        P.lemma67.boundaryLongArcExistenceFields.selectedLongArc) :=
  actualBudgetFieldsOfConcreteAnglesAndLemma67
    P.classification P.angleWitness P.Subpolygon P.subpolygonData
    P.lemma67

def toConcreteBudgetTriangleSourceFields
    (P : ConcreteTopologyLemma67TriangleSourceFields.{u} C) :
    ConcreteBudgetTriangleSourceFields.{u} C where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.lemma67.boundaryLongArcExistenceFields
  triangleRun := P.triangleRun

def toActualTopologyArcInputs
    (P : ConcreteTopologyLemma67TriangleSourceFields.{u} C) :
    ActualTopologyArcInputs.{u} C :=
  P.toConcreteBudgetTriangleSourceFields.toActualTopologyArcInputs

theorem actualBudgetFields_lt_pi_div_three
    (P : ConcreteTopologyLemma67TriangleSourceFields.{u} C) :
    P.actualBudgetFields.geometricAngleBudget < Real.pi / 3 :=
  actualBudgetFieldsOfConcreteAnglesAndLemma67_lt_pi_div_three
    P.classification P.angleWitness P.Subpolygon P.subpolygonData
    P.lemma67

@[simp]
theorem toActualTopologyArcInputs_boundaryArc
    (P : ConcreteTopologyLemma67TriangleSourceFields.{u} C) :
    P.toActualTopologyArcInputs.boundaryArc =
      P.triangleRun.toFiniteWalkData.toBoundaryArcCertificate :=
  rfl

end ConcreteTopologyLemma67TriangleSourceFields

structure MinimalFailureConcreteTopologyLemma67TriangleSourceFields
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  source : ConcreteTopologyLemma67TriangleSourceFields.{u} C

namespace MinimalFailureConcreteTopologyLemma67TriangleSourceFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def toActualTopologyArcInputs
    (P :
      MinimalFailureConcreteTopologyLemma67TriangleSourceFields.{u}
        C hmin) :
    ActualTopologyArcInputs.{u} C :=
  P.source.toActualTopologyArcInputs

theorem nonempty_actualTopologyArcInputs
    (P :
      MinimalFailureConcreteTopologyLemma67TriangleSourceFields.{u}
        C hmin) :
    Nonempty (ActualTopologyArcInputs.{u} C) :=
  Nonempty.intro P.toActualTopologyArcInputs

end MinimalFailureConcreteTopologyLemma67TriangleSourceFields

structure MinimalFailureActualTopologyArcSourceFamily : Type (u + 1) where
  inputs :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteBudgetTriangleSourceFields.{u} C hmin

namespace MinimalFailureActualTopologyArcSourceFamily

def inputsFor
    (F : MinimalFailureActualTopologyArcSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    ActualTopologyArcInputs.{u} C :=
  (F.inputs C hmin).toActualTopologyArcInputs

theorem nonempty_inputsFor
    (F : MinimalFailureActualTopologyArcSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    Nonempty (ActualTopologyArcInputs.{u} C) :=
  Nonempty.intro (F.inputsFor C hmin)

end MinimalFailureActualTopologyArcSourceFamily

end

end ActualTopologyArcInputsProducerW18
end Swanepoel
end ErdosProblems1066
