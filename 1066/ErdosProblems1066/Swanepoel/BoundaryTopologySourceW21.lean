import ErdosProblems1066.Swanepoel.TopologyArcClosureW19
import ErdosProblems1066.Swanepoel.TriangleRunSelectorW17

set_option autoImplicit false

/-!
# W21 boundary/topology source bridge

This file names the exact boundary/Jordan data still needed to feed the W19
topology-arc source row.  It does not extract an outer face, enclosure, or
boundary arc from minimality.  Instead, it proves that once those data are
available in the existing boundary/topology formats, they convert to
`TopologyArcClosureW19.MinimalFailureTopologyArcSourceFields`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryTopologySourceW21

open BoundaryArcExtractionProofW15
open BoundaryArcFiniteWalkConstructionW16
open ExactOuterBoundaryTopologyW13
open TopologyArcClosureW19
open TopologyToBoundaryArcW14
open TriangleRunSelectorW17

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  ExactOuterBoundaryTopologyW13.CanonicalGraph C

abbrev TopologyFacts (C : _root_.UDConfig n) :=
  ExactOuterBoundaryTopologyW13.TopologyFacts C

abbrev ActualTopologyArcInputs (C : _root_.UDConfig n) :=
  TopologyArcClosureW19.ActualTopologyArcInputs.{u} C

abbrev W19TopologyArcSourceFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  TopologyArcClosureW19.MinimalFailureTopologyArcSourceFields.{u} C hmin

abbrev W19TopologyArcSourceFamily :=
  TopologyArcClosureW19.MinimalFailureTopologyArcSourceFamily.{u}

/-- The topology facts corresponding to explicit Jordan extraction data. -/
abbrev topologyOfJordanExtraction
    {C : _root_.UDConfig n}
    (J : JordanBoundaryExtraction.Data (CanonicalGraph C)) :
    TopologyFacts C :=
  JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData J

/-! ## Exact pointwise missing fields -/

/--
Exact pointwise source fields with the boundary arc supplied in the W14
extraction format.  The `jordan` field is the explicit outer-face/enclosure
payload; angle, subpolygon, long-arc, and arc extraction fields are attached to
the planar boundary generated from it.
-/
structure MinimalFailureJordanBoundaryExtractionSourceFields
    (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C) where
  jordan : JordanBoundaryExtraction.Data (CanonicalGraph C)
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)
  longArc :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields
      ((topologyOfJordanExtraction jordan).toPlanarBoundaryData
        outerAngleBounds Subpolygon subpolygonData)
  arcExtraction :
    BoundaryArcExtractionFields
      ((topologyOfJordanExtraction jordan).toPlanarBoundaryData
        outerAngleBounds Subpolygon subpolygonData)

namespace MinimalFailureJordanBoundaryExtractionSourceFields

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def topology
    (P : MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin) :
    TopologyFacts C :=
  topologyOfJordanExtraction P.jordan

def planarBoundary
    (P : MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  P.topology.toPlanarBoundaryData P.outerAngleBounds P.Subpolygon
    P.subpolygonData

def triangleRun
    (P : MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin) :
    BoundaryArcTriangleRun P.planarBoundary :=
  BoundaryArcSelector.triangleRunOfExtractionFields P.arcExtraction

def finiteWalk
    (P : MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin) :
    BoundaryArcFiniteWalkData P.planarBoundary :=
  P.triangleRun.toFiniteWalkData

def toTopologyTriangleSourceFields
    (P : MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin) :
    TopologyTrianglePipelineW17.TopologyTriangleSourceFields.{u} C where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

def toW19TopologyArcSourceFields
    (P : MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin) :
    W19TopologyArcSourceFields.{u} C hmin where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

def toActualTopologyArcInputs
    (P : MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin) :
    ActualTopologyArcInputs.{u} C :=
  P.toW19TopologyArcSourceFields.toActualTopologyArcInputs

@[simp]
theorem toW19TopologyArcSourceFields_planarBoundary
    (P : MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin) :
    P.toW19TopologyArcSourceFields.planarBoundary = P.planarBoundary :=
  rfl

@[simp]
theorem triangleRun_pIndex
    (P : MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin)
    (i : M8LabelsFromBoundaryInterface.M8BoundaryIndex) :
    P.triangleRun.pIndex i = P.arcExtraction.boundaryArc.pIndex i :=
  rfl

theorem nonempty_w19TopologyArcSourceFields
    (P : MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin) :
    Nonempty (W19TopologyArcSourceFields.{u} C hmin) :=
  Nonempty.intro P.toW19TopologyArcSourceFields

theorem nonempty_actualTopologyArcInputs
    (P : MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin) :
    Nonempty (ActualTopologyArcInputs.{u} C) :=
  Nonempty.intro P.toActualTopologyArcInputs

end MinimalFailureJordanBoundaryExtractionSourceFields

/--
The same exact pointwise source surface, but with the boundary input already in
the W16 thirteen-triangle-run format.
-/
structure MinimalFailureJordanBoundaryTriangleRunSourceFields
    (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C) where
  jordan : JordanBoundaryExtraction.Data (CanonicalGraph C)
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)
  longArc :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields
      ((topologyOfJordanExtraction jordan).toPlanarBoundaryData
        outerAngleBounds Subpolygon subpolygonData)
  triangleRun :
    BoundaryArcTriangleRun
      ((topologyOfJordanExtraction jordan).toPlanarBoundaryData
        outerAngleBounds Subpolygon subpolygonData)

namespace MinimalFailureJordanBoundaryTriangleRunSourceFields

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def topology
    (P : MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    TopologyFacts C :=
  topologyOfJordanExtraction P.jordan

def planarBoundary
    (P : MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  P.topology.toPlanarBoundaryData P.outerAngleBounds P.Subpolygon
    P.subpolygonData

def finiteWalk
    (P : MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    BoundaryArcFiniteWalkData P.planarBoundary :=
  P.triangleRun.toFiniteWalkData

def arcExtraction
    (P : MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    BoundaryArcExtractionFields P.planarBoundary :=
  P.finiteWalk.toBoundaryArcExtractionFields

def toExtractionSourceFields
    (P : MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin where
  jordan := P.jordan
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  arcExtraction := P.arcExtraction

def toTopologyTriangleSourceFields
    (P : MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    TopologyTrianglePipelineW17.TopologyTriangleSourceFields.{u} C where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

def toW19TopologyArcSourceFields
    (P : MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    W19TopologyArcSourceFields.{u} C hmin where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

def toActualTopologyArcInputs
    (P : MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    ActualTopologyArcInputs.{u} C :=
  P.toW19TopologyArcSourceFields.toActualTopologyArcInputs

@[simp]
theorem toW19TopologyArcSourceFields_planarBoundary
    (P : MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    P.toW19TopologyArcSourceFields.planarBoundary = P.planarBoundary :=
  rfl

@[simp]
theorem arcExtraction_boundaryArc
    (P : MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    P.arcExtraction.boundaryArc =
      P.triangleRun.toFiniteWalkData.toBoundaryArcCertificate :=
  rfl

theorem nonempty_w19TopologyArcSourceFields
    (P : MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    Nonempty (W19TopologyArcSourceFields.{u} C hmin) :=
  Nonempty.intro P.toW19TopologyArcSourceFields

theorem nonempty_actualTopologyArcInputs
    (P : MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    Nonempty (ActualTopologyArcInputs.{u} C) :=
  Nonempty.intro P.toActualTopologyArcInputs

end MinimalFailureJordanBoundaryTriangleRunSourceFields

/-! ## Conversion back from W19 rows -/

def jordanBoundaryTriangleRunSourceFieldsOfW19
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : W19TopologyArcSourceFields.{u} C hmin) :
    MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin where
  jordan := P.topology.toExtractionData
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := by
    change
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        ((JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData
            P.topology.toExtractionData).toPlanarBoundaryData
          P.outerAngleBounds P.Subpolygon P.subpolygonData)
    rw [JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData_toExtractionData]
    exact P.longArc
  triangleRun := by
    change
      BoundaryArcTriangleRun
        ((JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData
            P.topology.toExtractionData).toPlanarBoundaryData
          P.outerAngleBounds P.Subpolygon P.subpolygonData)
    rw [JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData_toExtractionData]
    exact P.triangleRun

def jordanBoundaryExtractionSourceFieldsOfW19
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : W19TopologyArcSourceFields.{u} C hmin) :
    MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin :=
  (jordanBoundaryTriangleRunSourceFieldsOfW19 P).toExtractionSourceFields

theorem nonempty_jordanBoundaryTriangleRunSourceFields_iff_w19
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Nonempty
        (MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin) <->
      Nonempty (W19TopologyArcSourceFields.{u} C hmin) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.toW19TopologyArcSourceFields⟩
  · rintro ⟨P⟩
    exact ⟨jordanBoundaryTriangleRunSourceFieldsOfW19 P⟩

theorem nonempty_jordanBoundaryExtractionSourceFields_iff_w19
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Nonempty
        (MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin) <->
      Nonempty (W19TopologyArcSourceFields.{u} C hmin) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.toW19TopologyArcSourceFields⟩
  · rintro ⟨P⟩
    exact ⟨jordanBoundaryExtractionSourceFieldsOfW19 P⟩

/-! ## Uniform family surfaces -/

structure MinimalFailureJordanBoundaryTriangleRunSourceFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        MinimalFailureJordanBoundaryTriangleRunSourceFields.{u} C hmin

namespace MinimalFailureJordanBoundaryTriangleRunSourceFamily

def toW19TopologyArcSourceFamily
    (F : MinimalFailureJordanBoundaryTriangleRunSourceFamily.{u}) :
    W19TopologyArcSourceFamily.{u} where
  row := fun C hmin => (F.row C hmin).toW19TopologyArcSourceFields

def inputsFor
    (F : MinimalFailureJordanBoundaryTriangleRunSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    ActualTopologyArcInputs.{u} C :=
  (F.row C hmin).toActualTopologyArcInputs

theorem nonempty_w19TopologyArcSourceFamily
    (F : MinimalFailureJordanBoundaryTriangleRunSourceFamily.{u}) :
    Nonempty W19TopologyArcSourceFamily.{u} :=
  Nonempty.intro F.toW19TopologyArcSourceFamily

@[simp]
theorem toW19TopologyArcSourceFamily_row
    (F : MinimalFailureJordanBoundaryTriangleRunSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (F.toW19TopologyArcSourceFamily.row C hmin).toActualTopologyArcInputs =
      (F.row C hmin).toActualTopologyArcInputs :=
  rfl

end MinimalFailureJordanBoundaryTriangleRunSourceFamily

structure MinimalFailureJordanBoundaryExtractionSourceFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        MinimalFailureJordanBoundaryExtractionSourceFields.{u} C hmin

namespace MinimalFailureJordanBoundaryExtractionSourceFamily

def toTriangleRunSourceFamily
    (F : MinimalFailureJordanBoundaryExtractionSourceFamily.{u}) :
    MinimalFailureJordanBoundaryTriangleRunSourceFamily.{u} where
  row := fun C hmin =>
    (F.row C hmin).toW19TopologyArcSourceFields
      |> jordanBoundaryTriangleRunSourceFieldsOfW19

def toW19TopologyArcSourceFamily
    (F : MinimalFailureJordanBoundaryExtractionSourceFamily.{u}) :
    W19TopologyArcSourceFamily.{u} where
  row := fun C hmin => (F.row C hmin).toW19TopologyArcSourceFields

def inputsFor
    (F : MinimalFailureJordanBoundaryExtractionSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    ActualTopologyArcInputs.{u} C :=
  (F.row C hmin).toActualTopologyArcInputs

theorem nonempty_w19TopologyArcSourceFamily
    (F : MinimalFailureJordanBoundaryExtractionSourceFamily.{u}) :
    Nonempty W19TopologyArcSourceFamily.{u} :=
  Nonempty.intro F.toW19TopologyArcSourceFamily

@[simp]
theorem toW19TopologyArcSourceFamily_row
    (F : MinimalFailureJordanBoundaryExtractionSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (F.toW19TopologyArcSourceFamily.row C hmin).toActualTopologyArcInputs =
      (F.row C hmin).toActualTopologyArcInputs :=
  rfl

end MinimalFailureJordanBoundaryExtractionSourceFamily

end

end BoundaryTopologySourceW21
end Swanepoel
end ErdosProblems1066
