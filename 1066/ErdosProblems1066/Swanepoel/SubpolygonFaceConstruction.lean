import ErdosProblems1066.Swanepoel.PlanarBoundaryFinal
import ErdosProblems1066.Swanepoel.SubpolygonDataConcrete
import ErdosProblems1066.Swanepoel.OuterBoundaryCoreConstruction

set_option autoImplicit false

/-!
# Subpolygon face construction facade

This module connects the checked outer-core/topology frontier to the concrete
subpolygon-family structures.  It keeps the geometry explicit: an
`OuterBoundaryCore` (or one produced from
`OuterBoundaryCoreConstruction.EnclosureData`) supplies the face-boundary
witness, while `SubpolygonDataConcrete` supplies the finite induced
subpolygon data and real angle comparisons.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonFaceConstruction

open BoundaryCounting
open FaceReduction
open SubpolygonAssembly
open SubpolygonDataConcrete

universe u

noncomputable section

variable {n : Nat}
variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-! ## Core data projected from the topology-construction frontier -/

/-- The checked outer-boundary core obtained from enclosure data. -/
def coreOfEnclosureData
    {T : OuterBoundaryCoreConstruction.OuterFaceData.{u} G}
    (E : OuterBoundaryCoreConstruction.EnclosureData T) :
    OuterBoundaryCore G :=
  OuterBoundaryCoreConstruction.EnclosureData.toCore E

@[simp]
theorem coreOfEnclosureData_faceBoundary
    {T : OuterBoundaryCoreConstruction.OuterFaceData.{u} G}
    (E : OuterBoundaryCoreConstruction.EnclosureData T) :
    (coreOfEnclosureData E).faceBoundary = T.faceBoundary :=
  rfl

@[simp]
theorem coreOfEnclosureData_outerFace
    {T : OuterBoundaryCoreConstruction.OuterFaceData.{u} G}
    (E : OuterBoundaryCoreConstruction.EnclosureData T) :
    (coreOfEnclosureData E).outerFace = T.outerFace :=
  rfl

@[simp]
theorem coreOfEnclosureData_outerEnclosure
    {T : OuterBoundaryCoreConstruction.OuterFaceData.{u} G}
    (E : OuterBoundaryCoreConstruction.EnclosureData T) :
    (coreOfEnclosureData E).outerEnclosure = E.outerEnclosure :=
  rfl

/-! ## Subpolygon-family projections to planar-boundary inputs -/

/-- The planar-boundary subpolygon inputs carried by a concrete core family. -/
def inputsOfCoreFamily
    (core : OuterBoundaryCore G)
    (F : CoreSubpolygonFamilyData.{u} core) :
    PlanarBoundarySubpolygonInputs.{u} G :=
  F.toPlanarBoundarySubpolygonInputs

@[simp]
theorem inputsOfCoreFamily_faceBoundary
    (core : OuterBoundaryCore G)
    (F : CoreSubpolygonFamilyData.{u} core) :
    (inputsOfCoreFamily core F).faceBoundary = core.faceBoundary :=
  rfl

@[simp]
theorem inputsOfCoreFamily_Subpolygon
    (core : OuterBoundaryCore G)
    (F : CoreSubpolygonFamilyData.{u} core) :
    (inputsOfCoreFamily core F).Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem inputsOfCoreFamily_subpolygonData
    (core : OuterBoundaryCore G)
    (F : CoreSubpolygonFamilyData.{u} core)
    (S : F.Subpolygon) :
    (inputsOfCoreFamily core F).subpolygonData S =
      (F.subpolygonData S).toSubpolygonCycleCountAngleData :=
  rfl

@[simp]
theorem inputsOfCoreFamily_subpolygonDegreeCounts
    (core : OuterBoundaryCore G)
    (F : CoreSubpolygonFamilyData.{u} core)
    (S : F.Subpolygon) :
    (inputsOfCoreFamily core F).subpolygonDegreeCounts S =
      (F.subpolygonData S).counts :=
  rfl

/-- The planar-boundary subpolygon inputs carried by a face-cycle family. -/
def inputsOfCoreFaceFamily
    (core : OuterBoundaryCore G)
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    PlanarBoundarySubpolygonInputs.{u} G :=
  F.toPlanarBoundarySubpolygonInputs

@[simp]
theorem inputsOfCoreFaceFamily_faceBoundary
    (core : OuterBoundaryCore G)
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    (inputsOfCoreFaceFamily core F).faceBoundary = core.faceBoundary :=
  rfl

@[simp]
theorem inputsOfCoreFaceFamily_Subpolygon
    (core : OuterBoundaryCore G)
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    (inputsOfCoreFaceFamily core F).Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem inputsOfCoreFaceFamily_subpolygonData
    (core : OuterBoundaryCore G)
    (F : CoreFaceSubpolygonFamilyData.{u} core)
    (S : F.Subpolygon) :
    (inputsOfCoreFaceFamily core F).subpolygonData S =
      (F.subpolygonData S).toSubpolygonCycleCountAngleData :=
  rfl

@[simp]
theorem inputsOfCoreFaceFamily_subpolygonDegreeCounts
    (core : OuterBoundaryCore G)
    (F : CoreFaceSubpolygonFamilyData.{u} core)
    (S : F.Subpolygon) :
    (inputsOfCoreFaceFamily core F).subpolygonDegreeCounts S =
      (F.subpolygonData S).counts :=
  rfl

/-- Enclosure data supplies the same face-boundary witness to a core family. -/
def inputsOfEnclosureDataCoreFamily
    {T : OuterBoundaryCoreConstruction.OuterFaceData.{u} G}
    (E : OuterBoundaryCoreConstruction.EnclosureData T)
    (F : CoreSubpolygonFamilyData.{u} (coreOfEnclosureData E)) :
    PlanarBoundarySubpolygonInputs.{u} G :=
  inputsOfCoreFamily (coreOfEnclosureData E) F

@[simp]
theorem inputsOfEnclosureDataCoreFamily_faceBoundary
    {T : OuterBoundaryCoreConstruction.OuterFaceData.{u} G}
    (E : OuterBoundaryCoreConstruction.EnclosureData T)
    (F : CoreSubpolygonFamilyData.{u} (coreOfEnclosureData E)) :
    (inputsOfEnclosureDataCoreFamily E F).faceBoundary = T.faceBoundary :=
  rfl

@[simp]
theorem inputsOfEnclosureDataCoreFamily_Subpolygon
    {T : OuterBoundaryCoreConstruction.OuterFaceData.{u} G}
    (E : OuterBoundaryCoreConstruction.EnclosureData T)
    (F : CoreSubpolygonFamilyData.{u} (coreOfEnclosureData E)) :
    (inputsOfEnclosureDataCoreFamily E F).Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem inputsOfEnclosureDataCoreFamily_subpolygonDegreeCounts
    {T : OuterBoundaryCoreConstruction.OuterFaceData.{u} G}
    (E : OuterBoundaryCoreConstruction.EnclosureData T)
    (F : CoreSubpolygonFamilyData.{u} (coreOfEnclosureData E))
    (S : F.Subpolygon) :
    (inputsOfEnclosureDataCoreFamily E F).subpolygonDegreeCounts S =
      (F.subpolygonData S).counts :=
  rfl

/-- Enclosure data supplies the same face-boundary witness to a face family. -/
def inputsOfEnclosureDataCoreFaceFamily
    {T : OuterBoundaryCoreConstruction.OuterFaceData.{u} G}
    (E : OuterBoundaryCoreConstruction.EnclosureData T)
    (F : CoreFaceSubpolygonFamilyData.{u} (coreOfEnclosureData E)) :
    PlanarBoundarySubpolygonInputs.{u} G :=
  inputsOfCoreFaceFamily (coreOfEnclosureData E) F

@[simp]
theorem inputsOfEnclosureDataCoreFaceFamily_faceBoundary
    {T : OuterBoundaryCoreConstruction.OuterFaceData.{u} G}
    (E : OuterBoundaryCoreConstruction.EnclosureData T)
    (F : CoreFaceSubpolygonFamilyData.{u} (coreOfEnclosureData E)) :
    (inputsOfEnclosureDataCoreFaceFamily E F).faceBoundary = T.faceBoundary :=
  rfl

@[simp]
theorem inputsOfEnclosureDataCoreFaceFamily_Subpolygon
    {T : OuterBoundaryCoreConstruction.OuterFaceData.{u} G}
    (E : OuterBoundaryCoreConstruction.EnclosureData T)
    (F : CoreFaceSubpolygonFamilyData.{u} (coreOfEnclosureData E)) :
    (inputsOfEnclosureDataCoreFaceFamily E F).Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem inputsOfEnclosureDataCoreFaceFamily_subpolygonDegreeCounts
    {T : OuterBoundaryCoreConstruction.OuterFaceData.{u} G}
    (E : OuterBoundaryCoreConstruction.EnclosureData T)
    (F : CoreFaceSubpolygonFamilyData.{u} (coreOfEnclosureData E))
    (S : F.Subpolygon) :
    (inputsOfEnclosureDataCoreFaceFamily E F).subpolygonDegreeCounts S =
      (F.subpolygonData S).counts :=
  rfl

/-! ## Planar-boundary data from core families -/

/-- Combine a core, outer angle bounds, and a concrete subpolygon family. -/
def planarBoundaryDataOfCoreFamily
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreSubpolygonFamilyData.{u} core) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  PlanarBoundaryFinal.PlanarBoundaryData.ofCoreOuterAngleBoundsSubpolygonInputs
    core outerAngleBounds (inputsOfCoreFamily core F) F.sameFaceBoundary

@[simp]
theorem planarBoundaryDataOfCoreFamily_core
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreSubpolygonFamilyData.{u} core) :
    (planarBoundaryDataOfCoreFamily core outerAngleBounds F).core = core :=
  rfl

@[simp]
theorem planarBoundaryDataOfCoreFamily_outerBoundaryCounts
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreSubpolygonFamilyData.{u} core) :
    (planarBoundaryDataOfCoreFamily core outerAngleBounds F).outerBoundaryCounts =
      outerAngleBounds.counts :=
  rfl

@[simp]
theorem planarBoundaryDataOfCoreFamily_faceBoundary
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreSubpolygonFamilyData.{u} core) :
    (planarBoundaryDataOfCoreFamily core outerAngleBounds F).faceBoundary =
      core.faceBoundary :=
  rfl

@[simp]
theorem planarBoundaryDataOfCoreFamily_Subpolygon
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreSubpolygonFamilyData.{u} core) :
    (planarBoundaryDataOfCoreFamily core outerAngleBounds F).Subpolygon =
      F.Subpolygon :=
  rfl

@[simp]
theorem planarBoundaryDataOfCoreFamily_subpolygonData
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreSubpolygonFamilyData.{u} core)
    (S : F.Subpolygon) :
    (planarBoundaryDataOfCoreFamily core outerAngleBounds F).subpolygonData S =
      (F.subpolygonData S).toSubpolygonCycleCountAngleData :=
  rfl

/-- Combine a core, outer angle bounds, and a face-boundary subpolygon family. -/
def planarBoundaryDataOfCoreFaceFamily
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  PlanarBoundaryFinal.PlanarBoundaryData.ofCoreOuterAngleBoundsSubpolygonInputs
    core outerAngleBounds (inputsOfCoreFaceFamily core F) F.sameFaceBoundary

@[simp]
theorem planarBoundaryDataOfCoreFaceFamily_core
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    (planarBoundaryDataOfCoreFaceFamily core outerAngleBounds F).core = core :=
  rfl

@[simp]
theorem planarBoundaryDataOfCoreFaceFamily_outerBoundaryCounts
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    (planarBoundaryDataOfCoreFaceFamily core outerAngleBounds F).outerBoundaryCounts =
      outerAngleBounds.counts :=
  rfl

@[simp]
theorem planarBoundaryDataOfCoreFaceFamily_faceBoundary
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    (planarBoundaryDataOfCoreFaceFamily core outerAngleBounds F).faceBoundary =
      core.faceBoundary :=
  rfl

@[simp]
theorem planarBoundaryDataOfCoreFaceFamily_Subpolygon
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    (planarBoundaryDataOfCoreFaceFamily core outerAngleBounds F).Subpolygon =
      F.Subpolygon :=
  rfl

@[simp]
theorem planarBoundaryDataOfCoreFaceFamily_subpolygonData
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreFaceSubpolygonFamilyData.{u} core)
    (S : F.Subpolygon) :
    (planarBoundaryDataOfCoreFaceFamily core outerAngleBounds F).subpolygonData S =
      (F.subpolygonData S).toSubpolygonCycleCountAngleData :=
  rfl

/-- Combine outer angle data and a concrete subpolygon family. -/
def planarBoundaryDataOfOuterAngleCoreFamily
    (outerData : OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G)
    (F : CoreSubpolygonFamilyData.{u} outerData.core) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  planarBoundaryDataOfCoreFamily outerData.core outerData.angleBounds F

@[simp]
theorem planarBoundaryDataOfOuterAngleCoreFamily_core
    (outerData : OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G)
    (F : CoreSubpolygonFamilyData.{u} outerData.core) :
    (planarBoundaryDataOfOuterAngleCoreFamily outerData F).core =
      outerData.core :=
  rfl

@[simp]
theorem planarBoundaryDataOfOuterAngleCoreFamily_outerBoundaryCounts
    (outerData : OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G)
    (F : CoreSubpolygonFamilyData.{u} outerData.core) :
    (planarBoundaryDataOfOuterAngleCoreFamily outerData F).outerBoundaryCounts =
      outerData.counts :=
  rfl

/-! ## Concrete face-counting data and low-degree inequalities -/

/-- Concrete face-counting data extracted from a core subpolygon family. -/
def concreteFaceCountingDataOfCoreFamily
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreSubpolygonFamilyData.{u} core) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      (planarBoundaryDataOfCoreFamily core outerAngleBounds F) :=
  PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData
    (planarBoundaryDataOfCoreFamily core outerAngleBounds F)

@[simp]
theorem concreteFaceCountingDataOfCoreFamily_faceBoundary
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreSubpolygonFamilyData.{u} core) :
    (concreteFaceCountingDataOfCoreFamily core outerAngleBounds F).faceBoundary =
      core.faceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingDataOfCoreFamily_subpolygonCounts
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreSubpolygonFamilyData.{u} core)
    (S : F.Subpolygon) :
    (concreteFaceCountingDataOfCoreFamily core outerAngleBounds F).subpolygonCounts S =
      (F.subpolygonData S).counts :=
  rfl

/-- E13 with high-degree slack, projected from the explicit core-family fields. -/
theorem lowDegreeWithHighDegreeSlackOfCoreFamily
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreSubpolygonFamilyData.{u} core)
  (S : F.Subpolygon) :
    (F.subpolygonData S).counts.D5 +
        2 * (F.subpolygonData S).counts.D6 + 6 <=
      2 * (F.subpolygonData S).counts.D2 +
        (F.subpolygonData S).counts.D3 :=
  (concreteFaceCountingDataOfCoreFamily core outerAngleBounds F)
    |>.subpolygonLowDegreeWithHighDegreeSlack S

/-- Swanepoel's low-degree inequality, projected from the explicit fields. -/
theorem lowDegreeOfCoreFamily
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
  (F : CoreSubpolygonFamilyData.{u} core)
  (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonData S).counts.D2 +
      (F.subpolygonData S).counts.D3 :=
  (concreteFaceCountingDataOfCoreFamily core outerAngleBounds F).subpolygonLowDegree S

/-- Concrete face-counting data extracted from a face-boundary family. -/
def concreteFaceCountingDataOfCoreFaceFamily
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      (planarBoundaryDataOfCoreFaceFamily core outerAngleBounds F) :=
  PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData
    (planarBoundaryDataOfCoreFaceFamily core outerAngleBounds F)

@[simp]
theorem concreteFaceCountingDataOfCoreFaceFamily_faceBoundary
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreFaceSubpolygonFamilyData.{u} core) :
    (concreteFaceCountingDataOfCoreFaceFamily core outerAngleBounds F).faceBoundary =
      core.faceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingDataOfCoreFaceFamily_subpolygonCounts
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreFaceSubpolygonFamilyData.{u} core)
    (S : F.Subpolygon) :
    (concreteFaceCountingDataOfCoreFaceFamily core outerAngleBounds F).subpolygonCounts S =
      (F.subpolygonData S).counts :=
  rfl

/-- E13 with high-degree slack for face-boundary subpolygon families. -/
theorem lowDegreeWithHighDegreeSlackOfCoreFaceFamily
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (F : CoreFaceSubpolygonFamilyData.{u} core)
  (S : F.Subpolygon) :
    (F.subpolygonData S).counts.D5 +
        2 * (F.subpolygonData S).counts.D6 + 6 <=
      2 * (F.subpolygonData S).counts.D2 +
        (F.subpolygonData S).counts.D3 :=
  (concreteFaceCountingDataOfCoreFaceFamily core outerAngleBounds F)
    |>.subpolygonLowDegreeWithHighDegreeSlack S

/-- Swanepoel's low-degree inequality for face-boundary subpolygon families. -/
theorem lowDegreeOfCoreFaceFamily
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
  (F : CoreFaceSubpolygonFamilyData.{u} core)
  (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonData S).counts.D2 +
      (F.subpolygonData S).counts.D3 :=
  (concreteFaceCountingDataOfCoreFaceFamily core outerAngleBounds F).subpolygonLowDegree S

end

end SubpolygonFaceConstruction
end Swanepoel
end ErdosProblems1066
