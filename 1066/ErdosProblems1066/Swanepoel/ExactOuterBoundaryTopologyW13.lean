import ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete
import ErdosProblems1066.Swanepoel.TopologyInstantiationW11
import ErdosProblems1066.Swanepoel.BoundaryClassificationW12

set_option autoImplicit false

/-!
# W13 exact outer-boundary topology facade

This file keeps the W13 topology step at the precise frontier exposed by the
existing checked modules.  It does not create face/enclosure data from the
graph.  Instead, it records the exact projections from explicit topology
records into the minimal-failure topology field, and conversely identifies that
field with the W10/W11 checked topology targets.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace ExactOuterBoundaryTopologyW13

open FaceReduction
open OuterBoundaryInterface

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    CanonicalStraightLineUnitDistanceGraph n :=
  JordanTopologyFactsConcrete.canonicalGraph C

abbrev MinimalExactFields (C : _root_.UDConfig n) : Prop :=
  JordanTopologyFactsConcrete.MinimalFailureTopology.ExactOuterBoundaryTopologyFields C

abbrev MinimalCompletion (C : _root_.UDConfig n) : Prop :=
  JordanTopologyFactsConcrete.MinimalFailureTopology.MinimalFailureTopologyCompletion C

abbrev MinimalGraphRoute (C : _root_.UDConfig n) : Prop :=
  JordanTopologyFactsConcrete.MinimalFailureTopology.MinimalFailureGraphRoute C

abbrev TopologyFacts (C : _root_.UDConfig n) :=
  JordanTopologyFactsConcrete.TopologyFacts.{0} C

abbrev W10ExactFields (C : _root_.UDConfig n) :=
  TopologyFrontierW10.ExactOuterBoundaryTopologyFields C

abbrev W10ExactFieldTarget (C : _root_.UDConfig n) : Prop :=
  TopologyFrontierW10.ExactOuterBoundaryTopologyFieldTarget C

abbrev CheckedTopologyPackage (C : _root_.UDConfig n) :=
  TopologyInstantiationW11.CheckedTopologyPackage C

abbrev CheckedTopologyPackageTarget (C : _root_.UDConfig n) : Prop :=
  TopologyInstantiationW11.CheckedTopologyPackageTarget C

theorem exactFields_of_topologyFacts
    {C : _root_.UDConfig n} (T : TopologyFacts C) :
    MinimalExactFields C :=
  Exists.intro T.faceBoundary
    (Exists.intro T.outerFace
      (And.intro T.outerFace_isOuter (Nonempty.intro T.outerEnclosure)))

theorem exactFields_of_w10ExactFields
    {C : _root_.UDConfig n} (T : W10ExactFields C) :
    MinimalExactFields C :=
  Exists.intro T.faceBoundary
    (Exists.intro T.outerFace
      (And.intro T.outerFace_isOuter (Nonempty.intro T.outerEnclosure)))

theorem exactFields_of_outerBoundaryCore
    {C : _root_.UDConfig n}
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    MinimalExactFields C :=
  Exists.intro P.faceBoundary
    (Exists.intro P.outerFace
      (And.intro P.outerFace_isOuter (Nonempty.intro P.outerEnclosure)))

theorem exactFields_of_checkedTopologyPackage
    {C : _root_.UDConfig n} (P : CheckedTopologyPackage C) :
    MinimalExactFields C :=
  exactFields_of_w10ExactFields P.toExactFields

theorem exactFields_iff_topologyFacts
    (C : _root_.UDConfig n) :
    MinimalExactFields C <-> Nonempty (TopologyFacts C) :=
  JordanTopologyFactsConcrete.MinimalFailureTopology.exactOuterBoundaryTopologyFields_iff_topologyFacts
    C

theorem exactFields_iff_outerBoundaryCore
    (C : _root_.UDConfig n) :
    MinimalExactFields C <->
      Nonempty (OuterBoundaryCore.{0} (CanonicalGraph C)) :=
  JordanTopologyFactsConcrete.MinimalFailureTopology.exactOuterBoundaryTopologyFields_iff_outerBoundaryCore
    C

theorem exactFields_iff_w10ExactFieldTarget
    (C : _root_.UDConfig n) :
    MinimalExactFields C <-> W10ExactFieldTarget C := by
  constructor
  case mp =>
    intro h
    exact
      (TopologyFrontierW10.exactFieldTarget_iff_topologyFacts C).2
        ((exactFields_iff_topologyFacts C).1 h)
  case mpr =>
    intro h
    exact
      (exactFields_iff_topologyFacts C).2
        ((TopologyFrontierW10.exactFieldTarget_iff_topologyFacts C).1 h)

theorem exactFields_iff_checkedTopologyPackageTarget
    (C : _root_.UDConfig n) :
    MinimalExactFields C <-> CheckedTopologyPackageTarget C := by
  constructor
  case mp =>
    intro h
    exact
      (TopologyInstantiationW11.checkedTopologyPackageTarget_iff_exactFieldTarget
        C).2
        ((exactFields_iff_w10ExactFieldTarget C).1 h)
  case mpr =>
    intro h
    exact
      (exactFields_iff_w10ExactFieldTarget C).2
        ((TopologyInstantiationW11.checkedTopologyPackageTarget_iff_exactFieldTarget
          C).1 h)

theorem exactFields_iff_outerBoundaryExistenceExactTopologyFields
    (C : _root_.UDConfig n) :
    MinimalExactFields C <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C := by
  constructor
  case mp =>
    intro h
    exact
      (TopologyFrontierW10.exactFieldTarget_iff_exactTopologyFields C).1
        ((exactFields_iff_w10ExactFieldTarget C).1 h)
  case mpr =>
    intro h
    exact
      (exactFields_iff_w10ExactFieldTarget C).2
        ((TopologyFrontierW10.exactFieldTarget_iff_exactTopologyFields C).2 h)

theorem topologyFacts_of_exactFields
    {C : _root_.UDConfig n} (h : MinimalExactFields C) :
    Nonempty (TopologyFacts C) :=
  (exactFields_iff_topologyFacts C).1 h

theorem w10ExactFieldTarget_of_exactFields
    {C : _root_.UDConfig n} (h : MinimalExactFields C) :
    W10ExactFieldTarget C :=
  (exactFields_iff_w10ExactFieldTarget C).1 h

theorem checkedTopologyPackageTarget_of_exactFields
    {C : _root_.UDConfig n} (h : MinimalExactFields C) :
    CheckedTopologyPackageTarget C :=
  (exactFields_iff_checkedTopologyPackageTarget C).1 h

theorem completion_iff_exactFields_of_graphRoute
    {C : _root_.UDConfig n} (route : MinimalGraphRoute C) :
    MinimalCompletion C <-> MinimalExactFields C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro _ hfields =>
        exact hfields
  case mpr =>
    intro h
    exact Exists.intro route h

theorem completion_iff_topologyFacts_of_graphRoute
    {C : _root_.UDConfig n} (route : MinimalGraphRoute C) :
    MinimalCompletion C <-> Nonempty (TopologyFacts C) :=
  Iff.trans (completion_iff_exactFields_of_graphRoute route)
    (exactFields_iff_topologyFacts C)

theorem completion_iff_w10ExactFieldTarget_of_graphRoute
    {C : _root_.UDConfig n} (route : MinimalGraphRoute C) :
    MinimalCompletion C <-> W10ExactFieldTarget C :=
  Iff.trans (completion_iff_exactFields_of_graphRoute route)
    (exactFields_iff_w10ExactFieldTarget C)

theorem completion_iff_checkedTopologyPackageTarget_of_graphRoute
    {C : _root_.UDConfig n} (route : MinimalGraphRoute C) :
    MinimalCompletion C <-> CheckedTopologyPackageTarget C :=
  Iff.trans (completion_iff_exactFields_of_graphRoute route)
    (exactFields_iff_checkedTopologyPackageTarget C)

theorem completion_of_graphRoute_topologyFacts
    {C : _root_.UDConfig n} (route : MinimalGraphRoute C)
    (T : TopologyFacts C) :
    MinimalCompletion C :=
  (completion_iff_exactFields_of_graphRoute route).2
    (exactFields_of_topologyFacts T)

theorem completion_of_graphRoute_w10ExactFields
    {C : _root_.UDConfig n} (route : MinimalGraphRoute C)
    (T : W10ExactFields C) :
    MinimalCompletion C :=
  (completion_iff_exactFields_of_graphRoute route).2
    (exactFields_of_w10ExactFields T)

theorem completion_of_graphRoute_checkedTopologyPackage
    {C : _root_.UDConfig n} (route : MinimalGraphRoute C)
    (P : CheckedTopologyPackage C) :
    MinimalCompletion C :=
  (completion_iff_exactFields_of_graphRoute route).2
    (exactFields_of_checkedTopologyPackage P)

theorem completion_iff_w10ExactFieldTarget_of_minimalFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexFinal.RemainingNoCutSlackFact C) :
    MinimalCompletion C <-> W10ExactFieldTarget C :=
  completion_iff_w10ExactFieldTarget_of_graphRoute
    (JordanTopologyFactsConcrete.MinimalFailureTopology.graphRoute_of_minimalFailure_remainingSlack
      (C := C) hmin hslack)

theorem completion_iff_checkedTopologyPackageTarget_of_minimalFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexFinal.RemainingNoCutSlackFact C) :
    MinimalCompletion C <-> CheckedTopologyPackageTarget C :=
  completion_iff_checkedTopologyPackageTarget_of_graphRoute
    (JordanTopologyFactsConcrete.MinimalFailureTopology.graphRoute_of_minimalFailure_remainingSlack
      (C := C) hmin hslack)

theorem completion_of_minimalFailure_topologyFacts
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexFinal.RemainingNoCutSlackFact C)
    (T : TopologyFacts C) :
    MinimalCompletion C :=
  (JordanTopologyFactsConcrete.MinimalFailureTopology.minimalFailureTopologyCompletion_iff_topologyFacts_of_minimalFailure
    (C := C) hmin hslack).2 (Nonempty.intro T)

theorem completion_of_minimalFailure_w10ExactFields
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexFinal.RemainingNoCutSlackFact C)
    (T : W10ExactFields C) :
    MinimalCompletion C :=
  (completion_iff_w10ExactFieldTarget_of_minimalFailure hmin hslack).2
    (Nonempty.intro T)

theorem completion_of_minimalFailure_checkedTopologyPackage
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexFinal.RemainingNoCutSlackFact C)
    (P : CheckedTopologyPackage C) :
    MinimalCompletion C :=
  (completion_iff_checkedTopologyPackageTarget_of_minimalFailure
    hmin hslack).2 (Nonempty.intro P)

def boundaryBookkeepingOfTopologyFacts
    {C : _root_.UDConfig n}
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (CanonicalGraph C)) :
    BoundaryClassification.BoundaryBookkeeping.{u} :=
  BoundaryClassificationW12.PlanarBoundaryData.boundaryBookkeeping
    (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)

@[simp]
theorem boundaryBookkeepingOfTopologyFacts_toBoundaryCounts
    {C : _root_.UDConfig n}
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (CanonicalGraph C)) :
    (boundaryBookkeepingOfTopologyFacts
      T outerAngleBounds Subpolygon subpolygonData).toBoundaryCounts =
        outerAngleBounds.counts := by
  change
    (BoundaryClassificationW12.PlanarBoundaryData.boundaryBookkeeping
      (T.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)).toBoundaryCounts = outerAngleBounds.counts
  exact
    BoundaryClassificationW12.PlanarBoundaryData.boundaryBookkeeping_toBoundaryCounts
      (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)

theorem boundaryBookkeepingOfTopologyFacts_angleCount
    {C : _root_.UDConfig n}
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (CanonicalGraph C)) :
    (boundaryBookkeepingOfTopologyFacts
      T outerAngleBounds Subpolygon subpolygonData).d5 +
          2 * (boundaryBookkeepingOfTopologyFacts
            T outerAngleBounds Subpolygon subpolygonData).d6 +
        (boundaryBookkeepingOfTopologyFacts
          T outerAngleBounds Subpolygon subpolygonData).b +
          (boundaryBookkeepingOfTopologyFacts
            T outerAngleBounds Subpolygon subpolygonData).longArcCount + 6 <=
      (boundaryBookkeepingOfTopologyFacts
        T outerAngleBounds Subpolygon subpolygonData).d3 := by
  change
    (BoundaryClassificationW12.PlanarBoundaryData.boundaryBookkeeping
      (T.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)).d5 +
          2 * (BoundaryClassificationW12.PlanarBoundaryData.boundaryBookkeeping
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData)).d6 +
        (BoundaryClassificationW12.PlanarBoundaryData.boundaryBookkeeping
          (T.toPlanarBoundaryData outerAngleBounds Subpolygon
            subpolygonData)).b +
          (BoundaryClassificationW12.PlanarBoundaryData.boundaryBookkeeping
            (T.toPlanarBoundaryData outerAngleBounds Subpolygon
              subpolygonData)).longArcCount + 6 <=
      (BoundaryClassificationW12.PlanarBoundaryData.boundaryBookkeeping
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)).d3
  exact
    BoundaryClassificationW12.PlanarBoundaryData.boundaryAngleCount_bookkeeping
      (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)

theorem boundaryBookkeepingOfTopologyFacts_negativeCount
    {C : _root_.UDConfig n}
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (CanonicalGraph C)) :
    (boundaryBookkeepingOfTopologyFacts
      T outerAngleBounds Subpolygon subpolygonData).negativeElementCount +
        (boundaryBookkeepingOfTopologyFacts
          T outerAngleBounds Subpolygon subpolygonData).longArcCount + 6 <=
      (boundaryBookkeepingOfTopologyFacts
        T outerAngleBounds Subpolygon subpolygonData).d3 := by
  change
    (BoundaryClassificationW12.PlanarBoundaryData.boundaryBookkeeping
      (T.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)).negativeElementCount +
        (BoundaryClassificationW12.PlanarBoundaryData.boundaryBookkeeping
          (T.toPlanarBoundaryData outerAngleBounds Subpolygon
            subpolygonData)).longArcCount + 6 <=
      (BoundaryClassificationW12.PlanarBoundaryData.boundaryBookkeeping
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)).d3
  exact
    BoundaryClassificationW12.PlanarBoundaryData.boundaryNegativeCount_bookkeeping
      (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)

end

end ExactOuterBoundaryTopologyW13
end Swanepoel
end ErdosProblems1066
