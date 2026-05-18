import ErdosProblems1066.Swanepoel.BoundaryArcFiniteWalkConstructionW16

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyTrianglePipelineW17

open BoundaryArcExtractionProofW15
open BoundaryArcFiniteWalkConstructionW16
open ExactOuterBoundaryTopologyW13
open TopologyToBoundaryArcW14

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  ExactOuterBoundaryTopologyW13.CanonicalGraph C

abbrev ExactTopologyFields (C : _root_.UDConfig n) : Prop :=
  ExactOuterBoundaryTopologyW13.MinimalExactFields C

abbrev TopologyArcFields (C : _root_.UDConfig n) : Type (u + 1) :=
  TopologyToBoundaryArcW14.TopologyBoundaryArcFields.{u} C

def TriangleRunTarget
    {C : _root_.UDConfig n}
    (R : TopologyArcFields.{u} C) : Prop :=
  Nonempty (BoundaryArcTriangleRun R.planarBoundary)

def FiniteWalkTarget
    {C : _root_.UDConfig n}
    (R : TopologyArcFields.{u} C) : Prop :=
  BoundaryArcFiniteWalkTarget
    R.topology R.outerAngleBounds R.Subpolygon R.subpolygonData R.longArc

theorem finiteWalkTarget_of_triangleRunTarget
    {C : _root_.UDConfig n}
    (R : TopologyArcFields.{u} C)
    (h : TriangleRunTarget R) :
    FiniteWalkTarget R := by
  cases h with
  | intro run =>
      exact finiteWalkTarget_of_triangleRun run

theorem extractionTarget_of_triangleRunTarget
    {C : _root_.UDConfig n}
    (R : TopologyArcFields.{u} C)
    (h : TriangleRunTarget R) :
    BoundaryArcExtractionTarget
      R.topology R.outerAngleBounds R.Subpolygon R.subpolygonData R.longArc := by
  exact
    extractionTarget_of_finiteWalkTarget
      (finiteWalkTarget_of_triangleRunTarget R h)

theorem extractionTarget_of_finiteWalkTarget
    {C : _root_.UDConfig n}
    (R : TopologyArcFields.{u} C)
    (h : FiniteWalkTarget R) :
    BoundaryArcExtractionTarget
      R.topology R.outerAngleBounds R.Subpolygon R.subpolygonData R.longArc :=
  BoundaryArcExtractionProofW15.extractionTarget_of_finiteWalkTarget h

structure TopologyTriangleSourceFields
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

namespace TopologyTriangleSourceFields

variable {C : _root_.UDConfig n}

def planarBoundary
    (R : TopologyTriangleSourceFields.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  R.topology.toPlanarBoundaryData R.outerAngleBounds R.Subpolygon
    R.subpolygonData

def exactTopologyFields
    (R : TopologyTriangleSourceFields.{u} C) :
    ExactTopologyFields C :=
  exactFields_of_topologyFacts R.topology

def finiteWalkData
    (R : TopologyTriangleSourceFields.{u} C) :
    BoundaryArcFiniteWalkData R.planarBoundary :=
  R.triangleRun.toFiniteWalkData

def finiteWalkTarget
    (R : TopologyTriangleSourceFields.{u} C) :
    BoundaryArcFiniteWalkTarget
      R.topology R.outerAngleBounds R.Subpolygon R.subpolygonData
      R.longArc :=
  finiteWalkTarget_of_triangleRun R.triangleRun

def extractionTarget
    (R : TopologyTriangleSourceFields.{u} C) :
    BoundaryArcExtractionTarget
      R.topology R.outerAngleBounds R.Subpolygon R.subpolygonData
      R.longArc :=
  BoundaryArcFiniteWalkConstructionW16.extractionTarget_of_triangleRun
    R.triangleRun

def arcExtraction
    (R : TopologyTriangleSourceFields.{u} C) :
    BoundaryArcExtractionFields R.planarBoundary :=
  R.finiteWalkData.toBoundaryArcExtractionFields

def toTopologyArcFields
    (R : TopologyTriangleSourceFields.{u} C) :
    TopologyArcFields.{u} C where
  topology := R.topology
  outerAngleBounds := R.outerAngleBounds
  Subpolygon := R.Subpolygon
  subpolygonData := R.subpolygonData
  longArc := R.longArc
  arcExtraction := R.arcExtraction

@[simp]
theorem toTopologyArcFields_planarBoundary
    (R : TopologyTriangleSourceFields.{u} C) :
    R.toTopologyArcFields.planarBoundary = R.planarBoundary :=
  rfl

@[simp]
theorem toTopologyArcFields_boundaryArc
    (R : TopologyTriangleSourceFields.{u} C) :
    R.toTopologyArcFields.boundaryArc =
      R.finiteWalkData.toBoundaryArcCertificate :=
  rfl

end TopologyTriangleSourceFields

structure TopologyFiniteWalkSourceFields
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
  finiteWalk :
    BoundaryArcFiniteWalkData
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)

namespace TopologyFiniteWalkSourceFields

variable {C : _root_.UDConfig n}

def planarBoundary
    (R : TopologyFiniteWalkSourceFields.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  R.topology.toPlanarBoundaryData R.outerAngleBounds R.Subpolygon
    R.subpolygonData

def exactTopologyFields
    (R : TopologyFiniteWalkSourceFields.{u} C) :
    ExactTopologyFields C :=
  exactFields_of_topologyFacts R.topology

def finiteWalkTarget
    (R : TopologyFiniteWalkSourceFields.{u} C) :
    BoundaryArcFiniteWalkTarget
      R.topology R.outerAngleBounds R.Subpolygon R.subpolygonData
      R.longArc :=
  Nonempty.intro R.finiteWalk

def extractionTarget
    (R : TopologyFiniteWalkSourceFields.{u} C) :
    BoundaryArcExtractionTarget
      R.topology R.outerAngleBounds R.Subpolygon R.subpolygonData
      R.longArc :=
  BoundaryArcExtractionProofW15.extractionTarget_of_finiteWalkTarget
    R.finiteWalkTarget

def arcExtraction
    (R : TopologyFiniteWalkSourceFields.{u} C) :
    BoundaryArcExtractionFields R.planarBoundary :=
  R.finiteWalk.toBoundaryArcExtractionFields

def toTopologyArcFields
    (R : TopologyFiniteWalkSourceFields.{u} C) :
    TopologyArcFields.{u} C where
  topology := R.topology
  outerAngleBounds := R.outerAngleBounds
  Subpolygon := R.Subpolygon
  subpolygonData := R.subpolygonData
  longArc := R.longArc
  arcExtraction := R.arcExtraction

@[simp]
theorem toTopologyArcFields_planarBoundary
    (R : TopologyFiniteWalkSourceFields.{u} C) :
    R.toTopologyArcFields.planarBoundary = R.planarBoundary :=
  rfl

@[simp]
theorem toTopologyArcFields_boundaryArc
    (R : TopologyFiniteWalkSourceFields.{u} C) :
    R.toTopologyArcFields.boundaryArc =
      R.finiteWalk.toBoundaryArcCertificate :=
  rfl

end TopologyFiniteWalkSourceFields

theorem topologyArcFields_of_triangleSource
    {C : _root_.UDConfig n}
    (R : TopologyTriangleSourceFields.{u} C) :
    Nonempty (TopologyArcFields.{u} C) :=
  Nonempty.intro R.toTopologyArcFields

theorem topologyArcFields_of_finiteWalkSource
    {C : _root_.UDConfig n}
    (R : TopologyFiniteWalkSourceFields.{u} C) :
    Nonempty (TopologyArcFields.{u} C) :=
  Nonempty.intro R.toTopologyArcFields

end

end TopologyTrianglePipelineW17
end Swanepoel
end ErdosProblems1066
