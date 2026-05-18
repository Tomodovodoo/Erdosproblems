import ErdosProblems1066.Swanepoel.NoEarlyConcreteSourceFamilyW29

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W30 no-early route-data closure

This worker closes the W29 concrete no-early route datatype back over the
explicit W27/W28 route inputs.  It adds direct constructors from coverage plus
one concrete obstruction family, a conversion to and from the W28 route data,
and constructive blockers for the remaining component data.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyRouteDataClosureW30

open Lemma9NoEarlyObstructionInhabitationW25
open Lemma9NoEarlySourceRowsW28
open Lemma9ProducerFamilyW20
open Lemma9SourceFamilyConcreteW27
open NoEarlyConcreteSourceFamilyW29

universe u

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}

/-! ## Concrete constructors from component data -/

def routeDataOfCoverageAndK23Obstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8K23ObstructionRowFamily.{u} payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceRouteData.{u}
      payForCut topologyArc lemma8 :=
  routeDataOfK23Data
    { coverage := coverage
      obstruction := obstruction }

def routeDataOfCoverageAndThreeCommonNeighborObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8ThreeCommonNeighborObstructionRowFamily.{u}
        payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceRouteData.{u}
      payForCut topologyArc lemma8 :=
  routeDataOfThreeCommonNeighborData
    { coverage := coverage
      obstruction := obstruction }

def routeDataOfCoverageAndCommonNeighborObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8CommonNeighborCardObstructionRowFamily.{u}
        payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceRouteData.{u}
      payForCut topologyArc lemma8 :=
  routeDataOfCommonNeighborData
    { coverage := coverage
      obstruction := obstruction }

def routeDataOfCoverageAndLocalExclusionObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8LocalExclusionObstructionPackageFamily.{u}
        payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceRouteData.{u}
      payForCut topologyArc lemma8 :=
  routeDataOfLocalExclusionData
    { coverage := coverage
      obstruction := obstruction }

theorem nonempty_routeData_of_coverage_and_k23Obstruction
    (hcoverage :
      Nonempty
        (M8Lemma9NoEarlyCoverageFamily.{u}
          payForCut topologyArc lemma8))
    (hobstruction :
      Nonempty
        (M8K23ObstructionRowFamily.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (M8ConcreteNoEarlySourceRouteData.{u}
        payForCut topologyArc lemma8) := by
  cases hcoverage with
  | intro coverage =>
      cases hobstruction with
      | intro obstruction =>
          exact Nonempty.intro
            (routeDataOfCoverageAndK23Obstruction coverage obstruction)

theorem nonempty_routeData_of_coverage_and_threeCommonNeighborObstruction
    (hcoverage :
      Nonempty
        (M8Lemma9NoEarlyCoverageFamily.{u}
          payForCut topologyArc lemma8))
    (hobstruction :
      Nonempty
        (M8ThreeCommonNeighborObstructionRowFamily.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (M8ConcreteNoEarlySourceRouteData.{u}
        payForCut topologyArc lemma8) := by
  cases hcoverage with
  | intro coverage =>
      cases hobstruction with
      | intro obstruction =>
          exact Nonempty.intro
            (routeDataOfCoverageAndThreeCommonNeighborObstruction
              coverage obstruction)

theorem nonempty_routeData_of_coverage_and_commonNeighborObstruction
    (hcoverage :
      Nonempty
        (M8Lemma9NoEarlyCoverageFamily.{u}
          payForCut topologyArc lemma8))
    (hobstruction :
      Nonempty
        (M8CommonNeighborCardObstructionRowFamily.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (M8ConcreteNoEarlySourceRouteData.{u}
        payForCut topologyArc lemma8) := by
  cases hcoverage with
  | intro coverage =>
      cases hobstruction with
      | intro obstruction =>
          exact Nonempty.intro
            (routeDataOfCoverageAndCommonNeighborObstruction
              coverage obstruction)

theorem nonempty_routeData_of_coverage_and_localExclusionObstruction
    (hcoverage :
      Nonempty
        (M8Lemma9NoEarlyCoverageFamily.{u}
          payForCut topologyArc lemma8))
    (hobstruction :
      Nonempty
        (M8LocalExclusionObstructionPackageFamily.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (M8ConcreteNoEarlySourceRouteData.{u}
        payForCut topologyArc lemma8) := by
  cases hcoverage with
  | intro coverage =>
      cases hobstruction with
      | intro obstruction =>
          exact Nonempty.intro
            (routeDataOfCoverageAndLocalExclusionObstruction
              coverage obstruction)

/-! ## Interop with W28 route data -/

def toW28RouteFamilyData
    (D :
      M8ConcreteNoEarlySourceRouteData.{u}
        payForCut topologyArc lemma8) :
    M8NoEarlyRouteFamilyData.{u}
      payForCut topologyArc lemma8 :=
  match D with
  | M8ConcreteNoEarlySourceRouteData.k23 K =>
      Lemma9NoEarlySourceRowsW28.routeFamilyDataOfK23 K
  | M8ConcreteNoEarlySourceRouteData.threeCommonNeighbor K =>
      Lemma9NoEarlySourceRowsW28.routeFamilyDataOfThreeCommonNeighbor K
  | M8ConcreteNoEarlySourceRouteData.commonNeighbor K =>
      Lemma9NoEarlySourceRowsW28.routeFamilyDataOfCommonNeighbor K
  | M8ConcreteNoEarlySourceRouteData.localExclusion K =>
      Lemma9NoEarlySourceRowsW28.routeFamilyDataOfLocalExclusion K

def ofW28RouteFamilyData
    (D :
      M8NoEarlyRouteFamilyData.{u}
        payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceRouteData.{u}
      payForCut topologyArc lemma8 :=
  match D with
  | M8NoEarlyRouteFamilyData.k23 K =>
      routeDataOfK23Data K
  | M8NoEarlyRouteFamilyData.threeCommonNeighbor K =>
      routeDataOfThreeCommonNeighborData K
  | M8NoEarlyRouteFamilyData.commonNeighbor K =>
      routeDataOfCommonNeighborData K
  | M8NoEarlyRouteFamilyData.localExclusion K =>
      routeDataOfLocalExclusionData K

theorem nonempty_routeData_iff_w28RouteFamilyData :
    Nonempty
      (M8ConcreteNoEarlySourceRouteData.{u}
        payForCut topologyArc lemma8) <->
      Nonempty
        (M8NoEarlyRouteFamilyData.{u}
          payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro (toW28RouteFamilyData D)
  case mpr =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro (ofW28RouteFamilyData D)

theorem nonempty_sourceFamily_of_routeData
    (h :
      Nonempty
        (M8ConcreteNoEarlySourceRouteData.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Lemma9NoEarlySourceRowsW28.nonempty_sourceFamily_of_routeData
    ((nonempty_routeData_iff_w28RouteFamilyData
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8)).mp h)

theorem not_routeData_of_not_sourceFamily
    (hbad :
      Not
        (Nonempty
          (Lemma9NatLateTripleSourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8ConcreteNoEarlySourceRouteData.{u}
          payForCut topologyArc lemma8)) := by
  intro hroute
  exact hbad (nonempty_sourceFamily_of_routeData hroute)

/-! ## Exact component blockers -/

theorem nonempty_routeData_iff_coverage_and_obstruction :
    Nonempty
      (M8ConcreteNoEarlySourceRouteData.{u}
        payForCut topologyArc lemma8) <->
      Nonempty
        (M8Lemma9NoEarlyCoverageFamily.{u}
          payForCut topologyArc lemma8) /\
        (Nonempty
          (M8K23ObstructionRowFamily.{u}
            payForCut topologyArc lemma8) \/
          Nonempty
            (M8ThreeCommonNeighborObstructionRowFamily.{u}
              payForCut topologyArc lemma8) \/
            Nonempty
              (M8CommonNeighborCardObstructionRowFamily.{u}
                payForCut topologyArc lemma8) \/
              Nonempty
                (M8LocalExclusionObstructionPackageFamily.{u}
                  payForCut topologyArc lemma8)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        cases D with
        | k23 K =>
            exact And.intro
              (Nonempty.intro K.coverage)
              (Or.inl (Nonempty.intro K.obstruction))
        | threeCommonNeighbor K =>
            exact And.intro
              (Nonempty.intro K.coverage)
              (Or.inr (Or.inl (Nonempty.intro K.obstruction)))
        | commonNeighbor K =>
            exact And.intro
              (Nonempty.intro K.coverage)
              (Or.inr (Or.inr (Or.inl (Nonempty.intro K.obstruction))))
        | localExclusion K =>
            exact And.intro
              (Nonempty.intro K.coverage)
              (Or.inr (Or.inr (Or.inr (Nonempty.intro K.obstruction))))
  case mpr =>
    intro h
    cases h.1 with
    | intro coverage =>
        cases h.2 with
        | inl hK23 =>
            cases hK23 with
            | intro obstruction =>
                exact Nonempty.intro
                  (routeDataOfCoverageAndK23Obstruction coverage obstruction)
        | inr hRest =>
            cases hRest with
            | inl hThree =>
                cases hThree with
                | intro obstruction =>
                    exact Nonempty.intro
                      (routeDataOfCoverageAndThreeCommonNeighborObstruction
                        coverage obstruction)
            | inr hRest2 =>
                cases hRest2 with
                | inl hCommon =>
                    cases hCommon with
                    | intro obstruction =>
                        exact Nonempty.intro
                          (routeDataOfCoverageAndCommonNeighborObstruction
                            coverage obstruction)
                | inr hLocal =>
                    cases hLocal with
                    | intro obstruction =>
                        exact Nonempty.intro
                          (routeDataOfCoverageAndLocalExclusionObstruction
                            coverage obstruction)

theorem not_routeData_iff_not_coverage_and_obstruction :
    Not
      (Nonempty
        (M8ConcreteNoEarlySourceRouteData.{u}
          payForCut topologyArc lemma8)) <->
      Not
        (Nonempty
          (M8Lemma9NoEarlyCoverageFamily.{u}
            payForCut topologyArc lemma8) /\
          (Nonempty
            (M8K23ObstructionRowFamily.{u}
              payForCut topologyArc lemma8) \/
            Nonempty
              (M8ThreeCommonNeighborObstructionRowFamily.{u}
                payForCut topologyArc lemma8) \/
              Nonempty
                (M8CommonNeighborCardObstructionRowFamily.{u}
                  payForCut topologyArc lemma8) \/
                Nonempty
                  (M8LocalExclusionObstructionPackageFamily.{u}
                    payForCut topologyArc lemma8))) := by
  constructor
  case mp =>
    intro hbad hcomponents
    exact hbad
      ((nonempty_routeData_iff_coverage_and_obstruction
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr hcomponents)
  case mpr =>
    intro hbad hroute
    exact hbad
      ((nonempty_routeData_iff_coverage_and_obstruction
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp hroute)

theorem not_each_obstruction_of_not_routeData_and_coverage
    (hbad :
      Not
        (Nonempty
          (M8ConcreteNoEarlySourceRouteData.{u}
            payForCut topologyArc lemma8)))
    (hcoverage :
      Nonempty
        (M8Lemma9NoEarlyCoverageFamily.{u}
          payForCut topologyArc lemma8)) :
      Not
        (Nonempty
          (M8K23ObstructionRowFamily.{u}
            payForCut topologyArc lemma8)) /\
      Not
        (Nonempty
          (M8ThreeCommonNeighborObstructionRowFamily.{u}
            payForCut topologyArc lemma8)) /\
      Not
        (Nonempty
          (M8CommonNeighborCardObstructionRowFamily.{u}
            payForCut topologyArc lemma8)) /\
      Not
        (Nonempty
          (M8LocalExclusionObstructionPackageFamily.{u}
            payForCut topologyArc lemma8)) := by
  constructor
  case left =>
    intro hK23
    exact hbad
      ((nonempty_routeData_iff_coverage_and_obstruction
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
        (And.intro hcoverage (Or.inl hK23)))
  case right =>
    constructor
    case left =>
      intro hThree
      exact hbad
        ((nonempty_routeData_iff_coverage_and_obstruction
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)).mpr
          (And.intro hcoverage (Or.inr (Or.inl hThree))))
    case right =>
      constructor
      case left =>
        intro hCommon
        exact hbad
          ((nonempty_routeData_iff_coverage_and_obstruction
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8)).mpr
            (And.intro hcoverage (Or.inr (Or.inr (Or.inl hCommon)))))
      case right =>
        intro hLocal
        exact hbad
          ((nonempty_routeData_iff_coverage_and_obstruction
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8)).mpr
            (And.intro hcoverage (Or.inr (Or.inr (Or.inr hLocal)))))

end NoEarlyRouteDataClosureW30
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW30ConcreteNoEarlySourceRouteData
    (payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) :=
  Swanepoel.NoEarlyConcreteSourceFamilyW29.M8ConcreteNoEarlySourceRouteData.{u}
    payForCut topologyArc lemma8

theorem swanepoelW30_routeData_iff_w28RouteFamilyData
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    Nonempty
      (SwanepoelW30ConcreteNoEarlySourceRouteData
        payForCut topologyArc lemma8) <->
      Nonempty
        (Swanepoel.Lemma9NoEarlySourceRowsW28.M8NoEarlyRouteFamilyData.{u}
          payForCut topologyArc lemma8) :=
  Swanepoel.NoEarlyRouteDataClosureW30.nonempty_routeData_iff_w28RouteFamilyData
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem swanepoelW30_sourceFamily_of_routeData
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (h :
      Nonempty
        (SwanepoelW30ConcreteNoEarlySourceRouteData
          payForCut topologyArc lemma8)) :
    Nonempty
      (Swanepoel.Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Swanepoel.NoEarlyRouteDataClosureW30.nonempty_sourceFamily_of_routeData h

theorem swanepoelW30_noRouteData_of_not_sourceFamily
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (hbad :
      Not
        (Nonempty
          (Swanepoel.Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (SwanepoelW30ConcreteNoEarlySourceRouteData
          payForCut topologyArc lemma8)) :=
  Swanepoel.NoEarlyRouteDataClosureW30.not_routeData_of_not_sourceFamily
    hbad

end Verified
end ErdosProblems1066

end
