import ErdosProblems1066.Swanepoel.TopologyFrontierW10
import ErdosProblems1066.Swanepoel.TopologyExtractionFromNoncrossing
import ErdosProblems1066.Swanepoel.OuterBoundaryExistenceConcrete
import ErdosProblems1066.Swanepoel.JordanBoundaryConcrete

set_option autoImplicit false

/-!
# W11 topology instantiation package

This file narrows the W10 topology frontier to one compact checked inhabitant:
an `OuterBoundaryCore` for the canonical unit-distance graph.  The declarations
below prove that this smaller package projects back to every topology shape
used downstream: W10 exact fields, split selected-face/enclosure fields,
Jordan missing topology facts, extraction data, remaining core requirements,
and full planar-boundary data once the explicit angle/subpolygon inputs are
also supplied.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyInstantiationW11

open FaceReduction
open OuterBoundaryInterface

noncomputable section

universe u

variable {n : Nat}

/-! ## Canonical graph -/

/-- The canonical graph shared by the W10 and W11 topology frontiers. -/
abbrev canonicalGraph (C : _root_.UDConfig n) :
    CanonicalStraightLineUnitDistanceGraph n :=
  TopologyFrontierW10.canonicalGraph C

@[simp]
theorem canonicalGraph_eq_w10
    (C : _root_.UDConfig n) :
    canonicalGraph C = TopologyFrontierW10.canonicalGraph C :=
  rfl

@[simp]
theorem canonicalGraph_eq_extraction
    (C : _root_.UDConfig n) :
    canonicalGraph C =
      TopologyExtractionFromNoncrossing.canonicalGraph C :=
  TopologyFrontierW10.canonicalGraph_eq_topologyExtraction C

@[simp]
theorem canonicalGraph_eq_outerBoundaryExistence
    (C : _root_.UDConfig n) :
    canonicalGraph C =
      OuterBoundaryExistenceConcrete.canonicalGraph C :=
  TopologyFrontierW10.canonicalGraph_eq_outerBoundaryExistence C

@[simp]
theorem canonicalGraph_eq_jordanBoundaryConcrete
    (C : _root_.UDConfig n) :
    canonicalGraph C = JordanBoundaryConcrete.canonicalGraph C :=
  rfl

/-- The graph side is already concrete for every configuration. -/
theorem concreteGraphFacts (C : _root_.UDConfig n) :
    OuterBoundaryExistenceConcrete.ConcreteGraphFacts C :=
  TopologyFrontierW10.concreteGraphFacts C

/-! ## Compact topology package -/

/--
A compact W11 topology package.

The single field is already the downstream core object.  All other topology
records in the current pipeline are checked projections of this core.
-/
structure CheckedTopologyPackage (C : _root_.UDConfig n) where
  core : OuterBoundaryCore.{0} (canonicalGraph C)

namespace CheckedTopologyPackage

variable {C : _root_.UDConfig n}

/-- Forget the W11 wrapper and expose the checked outer-boundary core. -/
def toCore (P : CheckedTopologyPackage C) :
    OuterBoundaryCore.{0} (canonicalGraph C) :=
  P.core

/-- Expand the compact core into the W10 exact topology fields. -/
def toExactFields (P : CheckedTopologyPackage C) :
    TopologyFrontierW10.ExactOuterBoundaryTopologyFields C :=
  TopologyFrontierW10.ExactOuterBoundaryTopologyFields.ofCore P.core

/-- Selected outer-face fields used by the noncrossing extraction layer. -/
def toSelectedOuterFaceFields (P : CheckedTopologyPackage C) :
    TopologyExtractionFromNoncrossing.SelectedOuterFaceFields C :=
  P.toExactFields.toSelectedOuterFaceFields

/-- Enclosure fields over the selected outer face. -/
def toEnclosureFields
    (P : CheckedTopologyPackage C) :
    TopologyExtractionFromNoncrossing.EnclosureFields
      P.toSelectedOuterFaceFields :=
  P.toExactFields.toEnclosureFields

/-- The split exact topology fields from the extraction frontier. -/
def toSplitExactTopologyFields
    (P : CheckedTopologyPackage C) :
    TopologyExtractionFromNoncrossing.SplitExactTopologyFields C :=
  P.toExactFields.toSplitExactTopologyFields

/-- The raw exact topology proposition used by concrete outer-boundary existence. -/
def toExactTopologyFields
    (P : CheckedTopologyPackage C) :
    OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  P.toExactFields.toExactTopologyFields

/-- Concrete Jordan missing topology facts. -/
def toMissingTopologyFacts
    (P : CheckedTopologyPackage C) :
    JordanBoundaryConcrete.MissingTopologyFacts.{0} C :=
  P.toExactFields.toMissingTopologyFacts

/-- Concrete Jordan selected outer-face data. -/
def toMissingOuterFaceData
    (P : CheckedTopologyPackage C) :
    JordanBoundaryConcrete.MissingOuterFaceData.{0} C :=
  P.toExactFields.toMissingOuterFaceData

/-- Concrete Jordan enclosure data over the selected outer face. -/
def toMissingEnclosureData
    (P : CheckedTopologyPackage C) :
    JordanBoundaryConcrete.MissingEnclosureData.{0}
      P.toMissingOuterFaceData :=
  P.toExactFields.toMissingEnclosureData

/-- Extraction facade data consumed by the Jordan-boundary layer. -/
def toExtractionData
    (P : CheckedTopologyPackage C) :
    JordanBoundaryExtraction.Data.{0} (canonicalGraph C) :=
  P.toMissingTopologyFacts.toExtractionData

/-- Core-topology requirements used by the generic core construction layer. -/
def toCoreTopologyRequirements
    (P : CheckedTopologyPackage C) :
    OuterBoundaryCoreConstruction.CoreTopologyRequirements.{0}
      (canonicalGraph C) :=
  P.toExactFields.toCoreTopologyRequirements

/-- The W10 exact field target for this configuration. -/
theorem toExactFieldTarget
    (P : CheckedTopologyPackage C) :
    TopologyFrontierW10.ExactOuterBoundaryTopologyFieldTarget C :=
  Nonempty.intro P.toExactFields

/-- The earlier concrete noncrossing topology frontier. -/
theorem toConcreteNoncrossingTopologyFrontier
    (P : CheckedTopologyPackage C) :
    TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier C :=
  TopologyFrontierW10.concreteNoncrossingTopologyFrontier_of_exactFields
    P.toExactFields

/-- The W10 noncrossing-to-exact frontier. -/
theorem toNoncrossingToExactOuterBoundaryFrontier
    (P : CheckedTopologyPackage C) :
    TopologyFrontierW10.NoncrossingToExactOuterBoundaryFrontier C :=
  (TopologyFrontierW10.noncrossingToExactFrontier_iff_exactFieldTarget C).2
    P.toExactFieldTarget

/-- The remaining concrete core-topology target. -/
theorem toRemainingCoreTopologyRequirements
    (P : CheckedTopologyPackage C) :
    OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  TopologyFrontierW10.remainingCoreTopologyRequirements_of_exactFields
    P.toExactFields

/-- The remaining concrete Jordan topology theorem. -/
theorem toRemainingTopologyTheorem
    (P : CheckedTopologyPackage C) :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingTopologyTheorem C :=
  Nonempty.intro P.toMissingTopologyFacts

/-- Extend the compact topology package to final planar-boundary data. -/
def toPlanarBoundaryData
    (P : CheckedTopologyPackage C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (canonicalGraph C)) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u, 0}
      (canonicalGraph C) :=
  P.toExactFields.toPlanarBoundaryData
    outerAngleBounds Subpolygon subpolygonData

/-- Expose the concrete face-counting data after adding angle/subpolygon data. -/
def toConcreteFaceCountingData
    (P : CheckedTopologyPackage C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (canonicalGraph C)) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      (P.toPlanarBoundaryData
        outerAngleBounds Subpolygon subpolygonData) :=
  PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData _

@[simp]
theorem toCore_eq (P : CheckedTopologyPackage C) :
    P.toCore = P.core :=
  rfl

@[simp]
theorem toExactFields_toCore
    (P : CheckedTopologyPackage C) :
    P.toExactFields.toCore = P.core := by
  cases P with
  | mk core =>
      cases core
      rfl

@[simp]
theorem toMissingTopologyFacts_faceBoundary
    (P : CheckedTopologyPackage C) :
    P.toMissingTopologyFacts.faceBoundary = P.core.faceBoundary := by
  cases P with
  | mk core =>
      cases core
      rfl

@[simp]
theorem toMissingTopologyFacts_outerFace
    (P : CheckedTopologyPackage C) :
    P.toMissingTopologyFacts.outerFace = P.core.outerFace := by
  cases P with
  | mk core =>
      cases core
      rfl

theorem toMissingTopologyFacts_outerFace_isOuter
    (P : CheckedTopologyPackage C) :
    P.toMissingTopologyFacts.faceBoundary.IsOuterFace
      P.toMissingTopologyFacts.outerFace :=
  P.toMissingTopologyFacts.outerFace_isOuter

@[simp]
theorem toMissingTopologyFacts_outerEnclosure
    (P : CheckedTopologyPackage C) :
    P.toMissingTopologyFacts.outerEnclosure = P.core.outerEnclosure := by
  cases P with
  | mk core =>
      cases core
      rfl

@[simp]
theorem toExtractionData_faceBoundary
    (P : CheckedTopologyPackage C) :
    P.toExtractionData.faceBoundary = P.core.faceBoundary := by
  cases P with
  | mk core =>
      cases core
      rfl

@[simp]
theorem toExtractionData_outerFace
    (P : CheckedTopologyPackage C) :
    P.toExtractionData.outerFace = P.core.outerFace := by
  cases P with
  | mk core =>
      cases core
      rfl

@[simp]
theorem toExtractionData_outerEnclosure
    (P : CheckedTopologyPackage C) :
    P.toExtractionData.outerEnclosure = P.core.outerEnclosure := by
  cases P with
  | mk core =>
      cases core
      rfl

@[simp]
theorem toPlanarBoundaryData_core
    (P : CheckedTopologyPackage C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (canonicalGraph C)) :
    (P.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).core = P.core := by
  cases P with
  | mk core =>
      cases core
      rfl

@[simp]
theorem toPlanarBoundaryData_faceBoundary
    (P : CheckedTopologyPackage C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (canonicalGraph C)) :
    (P.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).faceBoundary =
        P.core.faceBoundary := by
  cases P with
  | mk core =>
      cases core
      rfl

@[simp]
theorem toPlanarBoundaryData_outerFace
    (P : CheckedTopologyPackage C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (canonicalGraph C)) :
    (P.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).outerFace =
        P.core.outerFace := by
  cases P with
  | mk core =>
      cases core
      rfl

end CheckedTopologyPackage

/-! ## Constructors from existing topology data -/

/-- Wrap an already checked outer-boundary core. -/
def ofCore
    {C : _root_.UDConfig n}
    (core : OuterBoundaryCore.{0} (canonicalGraph C)) :
    CheckedTopologyPackage C where
  core := core

/-- Build the compact W11 package from W10 exact topology fields. -/
def ofExactFields
    {C : _root_.UDConfig n}
    (T : TopologyFrontierW10.ExactOuterBoundaryTopologyFields C) :
    CheckedTopologyPackage C :=
  ofCore T.toCore

/-- Build the compact W11 package from concrete Jordan missing topology facts. -/
def ofMissingTopologyFacts
    {C : _root_.UDConfig n}
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    CheckedTopologyPackage C :=
  ofCore T.toCore

/-- Build the compact W11 package from concrete topology facts. -/
def ofTopologyFacts
    {C : _root_.UDConfig n}
    (T : JordanTopologyFactsConcrete.TopologyFacts.{0} C) :
    CheckedTopologyPackage C :=
  ofExactFields
    (TopologyFrontierW10.ExactOuterBoundaryTopologyFields.ofTopologyFacts T)

/-- Build the compact W11 package from extraction facade data. -/
def ofExtractionData
    {C : _root_.UDConfig n}
    (D : JordanBoundaryExtraction.Data.{0} (canonicalGraph C)) :
    CheckedTopologyPackage C :=
  ofCore D.toCore

/-- Build the compact W11 package from split selected-face/enclosure fields. -/
def ofSplitFields
    {C : _root_.UDConfig n}
    (D : TopologyExtractionFromNoncrossing.SelectedOuterFaceFields C)
    (E : TopologyExtractionFromNoncrossing.EnclosureFields D) :
    CheckedTopologyPackage C where
  core := {
    faceBoundary := D.faceBoundary
    outerFace := D.outerFace
    outerFace_isOuter := D.outerFace_isOuter
    outerEnclosure := E.outerEnclosure }

@[simp]
theorem ofCore_toCore
    {C : _root_.UDConfig n}
    (core : OuterBoundaryCore.{0} (canonicalGraph C)) :
    (ofCore core).toCore = core :=
  rfl

@[simp]
theorem ofExactFields_toExactFields
    {C : _root_.UDConfig n}
    (T : TopologyFrontierW10.ExactOuterBoundaryTopologyFields C) :
    (ofExactFields T).toExactFields = T := by
  simp [ofExactFields, ofCore, CheckedTopologyPackage.toExactFields]

@[simp]
theorem ofMissingTopologyFacts_toMissingTopologyFacts
    {C : _root_.UDConfig n}
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    (ofMissingTopologyFacts T).toMissingTopologyFacts = T := by
  cases T
  rfl

@[simp]
theorem ofExtractionData_toExtractionData
    {C : _root_.UDConfig n}
    (D : JordanBoundaryExtraction.Data.{0} (canonicalGraph C)) :
    (ofExtractionData D).toExtractionData = D := by
  cases D
  rfl

/-! ## Proposition-level frontier -/

/-- W11 frontier target: a nonempty compact checked topology package. -/
def CheckedTopologyPackageTarget
    (C : _root_.UDConfig n) : Prop :=
  Nonempty (CheckedTopologyPackage C)

/-- The W11 package target is exactly nonempty checked core data. -/
theorem checkedTopologyPackageTarget_iff_outerBoundaryCore
    (C : _root_.UDConfig n) :
    CheckedTopologyPackageTarget C <->
      Nonempty (OuterBoundaryCore.{0} (canonicalGraph C)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.core
  case mpr =>
    intro h
    cases h with
    | intro core =>
        exact Nonempty.intro (ofCore core)

/-- The W11 package target is equivalent to the W10 exact field target. -/
theorem checkedTopologyPackageTarget_iff_exactFieldTarget
    (C : _root_.UDConfig n) :
    CheckedTopologyPackageTarget C <->
      TopologyFrontierW10.ExactOuterBoundaryTopologyFieldTarget C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact P.toExactFieldTarget
  case mpr =>
    intro h
    cases h with
    | intro T =>
        exact Nonempty.intro (ofExactFields T)

/-- The W11 package target is equivalent to raw exact topology fields. -/
theorem checkedTopologyPackageTarget_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    CheckedTopologyPackageTarget C <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C := by
  constructor
  case mp =>
    intro h
    exact
      (TopologyFrontierW10.exactFieldTarget_iff_exactTopologyFields C).1
        ((checkedTopologyPackageTarget_iff_exactFieldTarget C).1 h)
  case mpr =>
    intro h
    exact
      (checkedTopologyPackageTarget_iff_exactFieldTarget C).2
        ((TopologyFrontierW10.exactFieldTarget_iff_exactTopologyFields C).2 h)

/-- The W11 package target is equivalent to concrete Jordan missing facts. -/
theorem checkedTopologyPackageTarget_iff_missingTopologyFacts
    (C : _root_.UDConfig n) :
    CheckedTopologyPackageTarget C <->
      Nonempty (JordanBoundaryConcrete.MissingTopologyFacts.{0} C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toMissingTopologyFacts
  case mpr =>
    intro h
    cases h with
    | intro T =>
        exact Nonempty.intro (ofMissingTopologyFacts T)

/-- The W11 package target is equivalent to the split extraction fields. -/
theorem checkedTopologyPackageTarget_iff_splitExactTopologyFields
    (C : _root_.UDConfig n) :
    CheckedTopologyPackageTarget C <->
      TopologyExtractionFromNoncrossing.SplitExactTopologyFields C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact P.toSplitExactTopologyFields
  case mpr =>
    intro h
    exact
      (checkedTopologyPackageTarget_iff_exactTopologyFields C).2
        ((TopologyExtractionFromNoncrossing.splitExactTopologyFields_iff_exactTopologyFields
          C).1 h)

/-- The W11 package target is equivalent to the concrete noncrossing frontier. -/
theorem checkedTopologyPackageTarget_iff_concreteNoncrossingTopologyFrontier
    (C : _root_.UDConfig n) :
    CheckedTopologyPackageTarget C <->
      TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact P.toConcreteNoncrossingTopologyFrontier
  case mpr =>
    intro h
    exact
      (checkedTopologyPackageTarget_iff_exactTopologyFields C).2
        ((TopologyExtractionFromNoncrossing.concreteNoncrossingTopologyFrontier_iff_exactTopologyFields
          C).1 h)

/-- W11 package data discharge the remaining core topology target. -/
theorem remainingCoreTopologyRequirements_of_checkedTopologyPackage
    {C : _root_.UDConfig n}
    (P : CheckedTopologyPackage C) :
    OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  P.toRemainingCoreTopologyRequirements

/-- The remaining core topology target is equivalent to the W11 package target. -/
theorem checkedTopologyPackageTarget_iff_remainingCoreTopologyRequirements
    (C : _root_.UDConfig n) :
    CheckedTopologyPackageTarget C <->
      OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact P.toRemainingCoreTopologyRequirements
  case mpr =>
    intro h
    exact
      (checkedTopologyPackageTarget_iff_exactTopologyFields C).2
        ((OuterBoundaryExistenceConcrete.remainingCoreTopologyRequirements_iff_exactTopologyFields
          C).1 h)

/-- The global core construction target is exactly the W11 package target. -/
theorem globalTarget_iff_checkedTopologyPackageTarget :
    OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget <->
      forall (n : Nat) (C : _root_.UDConfig n),
        CheckedTopologyPackageTarget C := by
  constructor
  case mp =>
    intro h n C
    exact
      (checkedTopologyPackageTarget_iff_exactFieldTarget C).2
        ((TopologyFrontierW10.globalTarget_iff_exactFieldTarget).1 h n C)
  case mpr =>
    intro h
    exact
      (TopologyFrontierW10.globalTarget_iff_exactFieldTarget).2
        (fun n C =>
          (checkedTopologyPackageTarget_iff_exactFieldTarget C).1 (h n C))

end

end TopologyInstantiationW11
end Swanepoel
end ErdosProblems1066
