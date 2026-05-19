import ErdosProblems1066.Swanepoel.NoEarlyConcreteRowsW31

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W32 no-early route coverage closure

This leaf sharpens the W31 no-early route surface by distributing the shared
coverage input across the four concrete obstruction families.  The positive
constructors below only build route data from actual coverage and obstruction
evidence.  The negative theorems record the exact blockers for those four
routes.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyRouteCoverageClosureW32

open Lemma9NoEarlyObstructionInhabitationW25
open Lemma9ProducerFamilyW20
open Lemma9SourceFamilyConcreteW27
open NoEarlyConcreteRowsW31
open NoEarlyConcreteSourceFamilyW29
open NoEarlyRouteDataClosureW30

universe u

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}

/-! ## Named route-coverage data -/

abbrev NoEarlyCoverageFamily : Type (u + 1) :=
  M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8

abbrev K23ObstructionFamily : Type (u + 1) :=
  M8K23ObstructionRowFamily.{u} payForCut topologyArc lemma8

abbrev ThreeCommonNeighborObstructionFamily : Type (u + 1) :=
  M8ThreeCommonNeighborObstructionRowFamily.{u}
    payForCut topologyArc lemma8

abbrev CommonNeighborObstructionFamily : Type (u + 1) :=
  M8CommonNeighborCardObstructionRowFamily.{u}
    payForCut topologyArc lemma8

abbrev LocalExclusionObstructionFamily : Type (u + 1) :=
  M8LocalExclusionObstructionPackageFamily.{u}
    payForCut topologyArc lemma8

abbrev K23RouteCoverageData : Type (u + 1) :=
  M8K23NoEarlySourceFamilyData.{u} payForCut topologyArc lemma8

abbrev ThreeCommonNeighborRouteCoverageData : Type (u + 1) :=
  M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
    payForCut topologyArc lemma8

abbrev CommonNeighborRouteCoverageData : Type (u + 1) :=
  M8CommonNeighborNoEarlySourceFamilyData.{u}
    payForCut topologyArc lemma8

abbrev LocalExclusionRouteCoverageData : Type (u + 1) :=
  M8LocalExclusionNoEarlySourceFamilyData.{u}
    payForCut topologyArc lemma8

abbrev ConcreteNoEarlyRouteData : Type (u + 1) :=
  M8ConcreteNoEarlySourceRouteData.{u}
    payForCut topologyArc lemma8

abbrev NoEarlyK23RouteCoverageAvailable : Prop :=
  Nonempty
      (NoEarlyCoverageFamily.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8)) /\
    Nonempty
      (K23ObstructionFamily.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8))

abbrev NoEarlyThreeCommonNeighborRouteCoverageAvailable : Prop :=
  Nonempty
      (NoEarlyCoverageFamily.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8)) /\
    Nonempty
      (ThreeCommonNeighborObstructionFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))

abbrev NoEarlyCommonNeighborRouteCoverageAvailable : Prop :=
  Nonempty
      (NoEarlyCoverageFamily.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8)) /\
    Nonempty
      (CommonNeighborObstructionFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))

abbrev NoEarlyLocalExclusionRouteCoverageAvailable : Prop :=
  Nonempty
      (NoEarlyCoverageFamily.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8)) /\
    Nonempty
      (LocalExclusionObstructionFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))

abbrev NoEarlyRouteCoverageAvailable : Prop :=
  NoEarlyK23RouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) \/
    NoEarlyThreeCommonNeighborRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) \/
      NoEarlyCommonNeighborRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) \/
        NoEarlyLocalExclusionRouteCoverageAvailable.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)

abbrev ExactNoEarlyRouteCoverageBlockers : Prop :=
  Not
      (NoEarlyK23RouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) /\
    Not
      (NoEarlyThreeCommonNeighborRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) /\
      Not
        (NoEarlyCommonNeighborRouteCoverageAvailable.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)) /\
        Not
          (NoEarlyLocalExclusionRouteCoverageAvailable.{u}
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8))

abbrev ExactK23RouteCoverageBlocker : Prop :=
  Not
      (Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) \/
    Not
      (Nonempty
        (K23ObstructionFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))

abbrev ExactThreeCommonNeighborRouteCoverageBlocker : Prop :=
  Not
      (Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) \/
    Not
      (Nonempty
        (ThreeCommonNeighborObstructionFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))

abbrev ExactCommonNeighborRouteCoverageBlocker : Prop :=
  Not
      (Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) \/
    Not
      (Nonempty
        (CommonNeighborObstructionFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))

abbrev ExactLocalExclusionRouteCoverageBlocker : Prop :=
  Not
      (Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) \/
    Not
      (Nonempty
        (LocalExclusionObstructionFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))

/-! ## Forward constructors from concrete route-coverage data -/

def k23RouteCoverageDataOfCoverageAndObstruction
    (coverage :
      NoEarlyCoverageFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    (obstruction :
      K23ObstructionFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    K23RouteCoverageData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) where
  coverage := coverage
  obstruction := obstruction

def threeCommonNeighborRouteCoverageDataOfCoverageAndObstruction
    (coverage :
      NoEarlyCoverageFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    (obstruction :
      ThreeCommonNeighborObstructionFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    ThreeCommonNeighborRouteCoverageData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) where
  coverage := coverage
  obstruction := obstruction

def commonNeighborRouteCoverageDataOfCoverageAndObstruction
    (coverage :
      NoEarlyCoverageFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    (obstruction :
      CommonNeighborObstructionFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    CommonNeighborRouteCoverageData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) where
  coverage := coverage
  obstruction := obstruction

def localExclusionRouteCoverageDataOfCoverageAndObstruction
    (coverage :
      NoEarlyCoverageFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    (obstruction :
      LocalExclusionObstructionFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    LocalExclusionRouteCoverageData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) where
  coverage := coverage
  obstruction := obstruction

def routeDataOfK23RouteCoverageData
    (D :
      K23RouteCoverageData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    ConcreteNoEarlyRouteData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  routeDataOfCoverageAndK23Obstruction D.coverage D.obstruction

def routeDataOfThreeCommonNeighborRouteCoverageData
    (D :
      ThreeCommonNeighborRouteCoverageData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    ConcreteNoEarlyRouteData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  routeDataOfCoverageAndThreeCommonNeighborObstruction
    D.coverage D.obstruction

def routeDataOfCommonNeighborRouteCoverageData
    (D :
      CommonNeighborRouteCoverageData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    ConcreteNoEarlyRouteData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  routeDataOfCoverageAndCommonNeighborObstruction
    D.coverage D.obstruction

def routeDataOfLocalExclusionRouteCoverageData
    (D :
      LocalExclusionRouteCoverageData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    ConcreteNoEarlyRouteData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  routeDataOfCoverageAndLocalExclusionObstruction
    D.coverage D.obstruction

def routeDataOfK23CoverageAndObstruction
    (coverage :
      NoEarlyCoverageFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    (obstruction :
      K23ObstructionFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    ConcreteNoEarlyRouteData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  routeDataOfK23RouteCoverageData
    (k23RouteCoverageDataOfCoverageAndObstruction
      coverage obstruction)

def routeDataOfThreeCommonNeighborCoverageAndObstruction
    (coverage :
      NoEarlyCoverageFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    (obstruction :
      ThreeCommonNeighborObstructionFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    ConcreteNoEarlyRouteData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  routeDataOfThreeCommonNeighborRouteCoverageData
    (threeCommonNeighborRouteCoverageDataOfCoverageAndObstruction
      coverage obstruction)

def routeDataOfCommonNeighborCoverageAndObstruction
    (coverage :
      NoEarlyCoverageFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    (obstruction :
      CommonNeighborObstructionFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    ConcreteNoEarlyRouteData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  routeDataOfCommonNeighborRouteCoverageData
    (commonNeighborRouteCoverageDataOfCoverageAndObstruction
      coverage obstruction)

def routeDataOfLocalExclusionCoverageAndObstruction
    (coverage :
      NoEarlyCoverageFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    (obstruction :
      LocalExclusionObstructionFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    ConcreteNoEarlyRouteData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  routeDataOfLocalExclusionRouteCoverageData
    (localExclusionRouteCoverageDataOfCoverageAndObstruction
      coverage obstruction)

/-! ## Direct projections from concrete route data -/

def coverageFamilyOfRouteData
    (D :
      ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    NoEarlyCoverageFamily.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  match D with
  | M8ConcreteNoEarlySourceRouteData.k23 K => K.coverage
  | M8ConcreteNoEarlySourceRouteData.threeCommonNeighbor K => K.coverage
  | M8ConcreteNoEarlySourceRouteData.commonNeighbor K => K.coverage
  | M8ConcreteNoEarlySourceRouteData.localExclusion K => K.coverage

def coverageRowOfRouteData
    (D :
      ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    M8Lemma9NoEarlyCoverageRow payForCut topologyArc lemma8 C hmin :=
  (coverageFamilyOfRouteData
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) D).row C hmin

def gapNegativeCoverageDataOfRouteData
    (D :
      ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Lemma6Lemma7AssemblyW13.GapNegativeCoverageData
      (RowBoundary payForCut topologyArc lemma8 C hmin)
      ((coverageRowOfRouteData
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) D C hmin).longArcCount) :=
  (coverageRowOfRouteData
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) D C hmin).coverage

def lemma9SourceFieldsOfRouteData
    (D :
      ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  NoEarlyConcreteRowsW31.sourceFieldsOfRouteData
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) D C hmin

def natLateTripleInputsOfRouteData
    (D :
      ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    LateTriplesInterface.M8NatLateTripleInputs
      (Lemma9ProducerFamilyW20.AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 C hmin).localLabels.predicates.data :=
  (lemma9SourceFieldsOfRouteData
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) D C hmin).natLateTripleInputs

def lemma9SourceFamilyOfRouteData
    (D :
      ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  NoEarlyConcreteRowsW31.sourceFamilyOfRouteData
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) D

theorem nonempty_routeData_of_k23_routeCoverage
    (h :
      NoEarlyK23RouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Nonempty
      (ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) := by
  exact nonempty_routeData_of_coverage_and_k23Obstruction
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) h.1 h.2

theorem nonempty_routeData_of_threeCommonNeighbor_routeCoverage
    (h :
      NoEarlyThreeCommonNeighborRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Nonempty
      (ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) := by
  exact nonempty_routeData_of_coverage_and_threeCommonNeighborObstruction
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) h.1 h.2

theorem nonempty_routeData_of_commonNeighbor_routeCoverage
    (h :
      NoEarlyCommonNeighborRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Nonempty
      (ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) := by
  exact nonempty_routeData_of_coverage_and_commonNeighborObstruction
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) h.1 h.2

theorem nonempty_routeData_of_localExclusion_routeCoverage
    (h :
      NoEarlyLocalExclusionRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Nonempty
      (ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) := by
  exact nonempty_routeData_of_coverage_and_localExclusionObstruction
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) h.1 h.2

theorem nonempty_sourceFamily_of_k23_routeCoverage
    (h :
      NoEarlyK23RouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h.1 with
  | intro coverage =>
      cases h.2 with
      | intro obstruction =>
          exact
            NoEarlyConcreteRowsW31.nonempty_sourceFamily_of_coverage_and_k23Obstruction
              (payForCut := payForCut) (topologyArc := topologyArc)
              (lemma8 := lemma8) coverage obstruction

theorem nonempty_sourceFamily_of_threeCommonNeighbor_routeCoverage
    (h :
      NoEarlyThreeCommonNeighborRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h.1 with
  | intro coverage =>
      cases h.2 with
      | intro obstruction =>
          exact
            NoEarlyConcreteRowsW31.nonempty_sourceFamily_of_coverage_and_threeCommonNeighborObstruction
              (payForCut := payForCut) (topologyArc := topologyArc)
              (lemma8 := lemma8) coverage obstruction

theorem nonempty_sourceFamily_of_commonNeighbor_routeCoverage
    (h :
      NoEarlyCommonNeighborRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h.1 with
  | intro coverage =>
      cases h.2 with
      | intro obstruction =>
          exact
            NoEarlyConcreteRowsW31.nonempty_sourceFamily_of_coverage_and_commonNeighborObstruction
              (payForCut := payForCut) (topologyArc := topologyArc)
              (lemma8 := lemma8) coverage obstruction

theorem nonempty_sourceFamily_of_localExclusion_routeCoverage
    (h :
      NoEarlyLocalExclusionRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h.1 with
  | intro coverage =>
      cases h.2 with
      | intro obstruction =>
          exact
            NoEarlyConcreteRowsW31.nonempty_sourceFamily_of_coverage_and_localExclusionObstruction
              (payForCut := payForCut) (topologyArc := topologyArc)
              (lemma8 := lemma8) coverage obstruction

/-- Concrete projection of the local-exclusion branch: actual coverage plus
an already packaged local-exclusion obstruction row gives the W25 no-early
source family directly. -/
def concreteNoEarlySourceFamilyOfLocalExclusionRouteCoverage
    (h :
      NoEarlyLocalExclusionRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    M8ConcreteNoEarlySourceFamily.{u} payForCut topologyArc lemma8 :=
  (localExclusionRouteCoverageDataOfCoverageAndObstruction
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) (Classical.choice h.1)
    (Classical.choice h.2)).toW25SourceFamily

/-- Nonempty form of the concrete local-exclusion branch projection. -/
theorem nonempty_concreteNoEarlySourceFamily_of_localExclusion_routeCoverage
    (h :
      NoEarlyLocalExclusionRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Nonempty
      (M8ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro
    (concreteNoEarlySourceFamilyOfLocalExclusionRouteCoverage
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h)

theorem nonempty_sourceFamily_of_routeCoverage
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h with
  | inl hK23 =>
      exact
        nonempty_sourceFamily_of_k23_routeCoverage
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8) hK23
  | inr hRest =>
      cases hRest with
      | inl hThree =>
          exact
            nonempty_sourceFamily_of_threeCommonNeighbor_routeCoverage
              (payForCut := payForCut) (topologyArc := topologyArc)
              (lemma8 := lemma8) hThree
      | inr hRest2 =>
          cases hRest2 with
          | inl hCommon =>
              exact
                nonempty_sourceFamily_of_commonNeighbor_routeCoverage
                  (payForCut := payForCut) (topologyArc := topologyArc)
                  (lemma8 := lemma8) hCommon
          | inr hLocal =>
              exact
                nonempty_sourceFamily_of_localExclusion_routeCoverage
                  (payForCut := payForCut) (topologyArc := topologyArc)
                  (lemma8 := lemma8) hLocal

/-! ## Positive route coverage from actual W25 source families -/

theorem localExclusion_routeCoverage_of_concreteNoEarlySourceFamily
    (h :
      Nonempty
        (M8ConcreteNoEarlySourceFamily.{u}
          payForCut topologyArc lemma8)) :
    NoEarlyLocalExclusionRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  And.intro
    (nonempty_coverageFamily_of_concreteNoEarlySourceFamily
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h)
    (nonempty_localExclusionObstructionPackageFamily_of_concreteNoEarlySourceFamily
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h)

theorem routeCoverage_of_concreteNoEarlySourceFamily
    (h :
      Nonempty
        (M8ConcreteNoEarlySourceFamily.{u}
          payForCut topologyArc lemma8)) :
    NoEarlyRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  Or.inr (Or.inr (Or.inr
    (localExclusion_routeCoverage_of_concreteNoEarlySourceFamily
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h)))

theorem routeData_of_concreteNoEarlySourceFamily
    (h :
      Nonempty
        (M8ConcreteNoEarlySourceFamily.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :=
  nonempty_routeData_of_concreteNoEarlySourceFamily
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) h

/-! ## Positive route coverage from the four concrete components -/

theorem k23_routeCoverage_of_coverage_and_obstruction
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))
    (hobstruction :
      Nonempty
        (K23ObstructionFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyK23RouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  And.intro hcoverage hobstruction

theorem threeCommonNeighbor_routeCoverage_of_coverage_and_obstruction
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))
    (hobstruction :
      Nonempty
        (ThreeCommonNeighborObstructionFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyThreeCommonNeighborRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  And.intro hcoverage hobstruction

theorem commonNeighbor_routeCoverage_of_coverage_and_obstruction
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))
    (hobstruction :
      Nonempty
        (CommonNeighborObstructionFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyCommonNeighborRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  And.intro hcoverage hobstruction

theorem localExclusion_routeCoverage_of_coverage_and_obstruction
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))
    (hobstruction :
      Nonempty
        (LocalExclusionObstructionFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyLocalExclusionRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  And.intro hcoverage hobstruction

theorem routeCoverage_of_coverage_and_k23Obstruction
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))
    (hobstruction :
      Nonempty
        (K23ObstructionFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  Or.inl
    (k23_routeCoverage_of_coverage_and_obstruction
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) hcoverage hobstruction)

theorem routeCoverage_of_coverage_and_threeCommonNeighborObstruction
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))
    (hobstruction :
      Nonempty
        (ThreeCommonNeighborObstructionFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  Or.inr (Or.inl
    (threeCommonNeighbor_routeCoverage_of_coverage_and_obstruction
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) hcoverage hobstruction))

theorem routeCoverage_of_coverage_and_commonNeighborObstruction
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))
    (hobstruction :
      Nonempty
        (CommonNeighborObstructionFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  Or.inr (Or.inr (Or.inl
    (commonNeighbor_routeCoverage_of_coverage_and_obstruction
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) hcoverage hobstruction)))

theorem routeCoverage_of_coverage_and_localExclusionObstruction
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))
    (hobstruction :
      Nonempty
        (LocalExclusionObstructionFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  Or.inr (Or.inr (Or.inr
    (localExclusion_routeCoverage_of_coverage_and_obstruction
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) hcoverage hobstruction)))

theorem k23_routeCoverage_of_routeCoverageData
    (h :
      Nonempty
        (K23RouteCoverageData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyK23RouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) := by
  cases h with
  | intro D =>
      exact
        k23_routeCoverage_of_coverage_and_obstruction
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)
          (Nonempty.intro D.coverage) (Nonempty.intro D.obstruction)

theorem threeCommonNeighbor_routeCoverage_of_routeCoverageData
    (h :
      Nonempty
        (ThreeCommonNeighborRouteCoverageData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyThreeCommonNeighborRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) := by
  cases h with
  | intro D =>
      exact
        threeCommonNeighbor_routeCoverage_of_coverage_and_obstruction
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)
          (Nonempty.intro D.coverage) (Nonempty.intro D.obstruction)

theorem commonNeighbor_routeCoverage_of_routeCoverageData
    (h :
      Nonempty
        (CommonNeighborRouteCoverageData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyCommonNeighborRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) := by
  cases h with
  | intro D =>
      exact
        commonNeighbor_routeCoverage_of_coverage_and_obstruction
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)
          (Nonempty.intro D.coverage) (Nonempty.intro D.obstruction)

theorem localExclusion_routeCoverage_of_routeCoverageData
    (h :
      Nonempty
        (LocalExclusionRouteCoverageData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyLocalExclusionRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) := by
  cases h with
  | intro D =>
      exact
        localExclusion_routeCoverage_of_coverage_and_obstruction
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)
          (Nonempty.intro D.coverage) (Nonempty.intro D.obstruction)

theorem routeCoverage_of_k23RouteCoverageData
    (h :
      Nonempty
        (K23RouteCoverageData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  Or.inl
    (k23_routeCoverage_of_routeCoverageData
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h)

theorem routeCoverage_of_threeCommonNeighborRouteCoverageData
    (h :
      Nonempty
        (ThreeCommonNeighborRouteCoverageData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  Or.inr (Or.inl
    (threeCommonNeighbor_routeCoverage_of_routeCoverageData
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h))

theorem routeCoverage_of_commonNeighborRouteCoverageData
    (h :
      Nonempty
        (CommonNeighborRouteCoverageData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  Or.inr (Or.inr (Or.inl
    (commonNeighbor_routeCoverage_of_routeCoverageData
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h)))

theorem routeCoverage_of_localExclusionRouteCoverageData
    (h :
      Nonempty
        (LocalExclusionRouteCoverageData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  Or.inr (Or.inr (Or.inr
    (localExclusion_routeCoverage_of_routeCoverageData
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h)))

/-! ## Exact positive route coverage equivalences -/

theorem nonempty_k23RouteCoverageData_iff :
    Nonempty
        (K23RouteCoverageData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)) <->
      NoEarlyK23RouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) :=
  Lemma9NoEarlySourceRowsW28.nonempty_k23Data_iff_coverage_and_k23Obstruction
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem nonempty_threeCommonNeighborRouteCoverageData_iff :
    Nonempty
        (ThreeCommonNeighborRouteCoverageData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)) <->
      NoEarlyThreeCommonNeighborRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) :=
  Lemma9NoEarlySourceRowsW28.nonempty_threeCommonNeighborData_iff_coverage_and_obstruction
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem nonempty_commonNeighborRouteCoverageData_iff :
    Nonempty
        (CommonNeighborRouteCoverageData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)) <->
      NoEarlyCommonNeighborRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) :=
  Lemma9NoEarlySourceRowsW28.nonempty_commonNeighborData_iff_coverage_and_obstruction
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem nonempty_localExclusionRouteCoverageData_iff :
    Nonempty
        (LocalExclusionRouteCoverageData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)) <->
      NoEarlyLocalExclusionRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) :=
  Lemma9NoEarlySourceRowsW28.nonempty_localExclusionData_iff_coverage_and_obstruction
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

/-! ## Exact per-route coverage blockers -/

theorem not_k23_routeCoverage_iff_exactK23RouteCoverageBlocker :
    Not
        (NoEarlyK23RouteCoverageAvailable.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)) <->
      ExactK23RouteCoverageBlocker.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) := by
  classical
  constructor
  case mp =>
    intro hbad
    by_cases hcoverage :
        Nonempty
          (NoEarlyCoverageFamily.{u}
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8))
    · exact Or.inr
        (fun hobstruction => hbad (And.intro hcoverage hobstruction))
    · exact Or.inl hcoverage
  case mpr =>
    intro hbad hroute
    cases hbad with
    | inl hcoverage =>
        exact hcoverage hroute.1
    | inr hobstruction =>
        exact hobstruction hroute.2

theorem not_threeCommonNeighbor_routeCoverage_iff_exactThreeCommonNeighborRouteCoverageBlocker :
    Not
        (NoEarlyThreeCommonNeighborRouteCoverageAvailable.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)) <->
      ExactThreeCommonNeighborRouteCoverageBlocker.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) := by
  classical
  constructor
  case mp =>
    intro hbad
    by_cases hcoverage :
        Nonempty
          (NoEarlyCoverageFamily.{u}
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8))
    · exact Or.inr
        (fun hobstruction => hbad (And.intro hcoverage hobstruction))
    · exact Or.inl hcoverage
  case mpr =>
    intro hbad hroute
    cases hbad with
    | inl hcoverage =>
        exact hcoverage hroute.1
    | inr hobstruction =>
        exact hobstruction hroute.2

theorem not_commonNeighbor_routeCoverage_iff_exactCommonNeighborRouteCoverageBlocker :
    Not
        (NoEarlyCommonNeighborRouteCoverageAvailable.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)) <->
      ExactCommonNeighborRouteCoverageBlocker.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) := by
  classical
  constructor
  case mp =>
    intro hbad
    by_cases hcoverage :
        Nonempty
          (NoEarlyCoverageFamily.{u}
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8))
    · exact Or.inr
        (fun hobstruction => hbad (And.intro hcoverage hobstruction))
    · exact Or.inl hcoverage
  case mpr =>
    intro hbad hroute
    cases hbad with
    | inl hcoverage =>
        exact hcoverage hroute.1
    | inr hobstruction =>
        exact hobstruction hroute.2

theorem not_localExclusion_routeCoverage_iff_exactLocalExclusionRouteCoverageBlocker :
    Not
        (NoEarlyLocalExclusionRouteCoverageAvailable.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)) <->
      ExactLocalExclusionRouteCoverageBlocker.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) := by
  classical
  constructor
  case mp =>
    intro hbad
    by_cases hcoverage :
        Nonempty
          (NoEarlyCoverageFamily.{u}
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8))
    · exact Or.inr
        (fun hobstruction => hbad (And.intro hcoverage hobstruction))
    · exact Or.inl hcoverage
  case mpr =>
    intro hbad hroute
    cases hbad with
    | inl hcoverage =>
        exact hcoverage hroute.1
    | inr hobstruction =>
        exact hobstruction hroute.2

theorem no_k23RouteCoverageData_iff_exactK23RouteCoverageBlocker :
    Not
        (Nonempty
          (K23RouteCoverageData.{u}
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8))) <->
      ExactK23RouteCoverageBlocker.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) :=
  (not_congr
    (nonempty_k23RouteCoverageData_iff
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))).trans
    (not_k23_routeCoverage_iff_exactK23RouteCoverageBlocker
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))

theorem no_threeCommonNeighborRouteCoverageData_iff_exactThreeCommonNeighborRouteCoverageBlocker :
    Not
        (Nonempty
          (ThreeCommonNeighborRouteCoverageData.{u}
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8))) <->
      ExactThreeCommonNeighborRouteCoverageBlocker.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) :=
  (not_congr
    (nonempty_threeCommonNeighborRouteCoverageData_iff
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))).trans
    (not_threeCommonNeighbor_routeCoverage_iff_exactThreeCommonNeighborRouteCoverageBlocker
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))

theorem no_commonNeighborRouteCoverageData_iff_exactCommonNeighborRouteCoverageBlocker :
    Not
        (Nonempty
          (CommonNeighborRouteCoverageData.{u}
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8))) <->
      ExactCommonNeighborRouteCoverageBlocker.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) :=
  (not_congr
    (nonempty_commonNeighborRouteCoverageData_iff
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))).trans
    (not_commonNeighbor_routeCoverage_iff_exactCommonNeighborRouteCoverageBlocker
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))

theorem no_localExclusionRouteCoverageData_iff_exactLocalExclusionRouteCoverageBlocker :
    Not
        (Nonempty
          (LocalExclusionRouteCoverageData.{u}
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8))) <->
      ExactLocalExclusionRouteCoverageBlocker.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) :=
  (not_congr
    (nonempty_localExclusionRouteCoverageData_iff
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))).trans
    (not_localExclusion_routeCoverage_iff_exactLocalExclusionRouteCoverageBlocker
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))

theorem routeData_nonempty_iff_routeCoverageData :
    Nonempty
        (ConcreteNoEarlyRouteData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)) <->
      Nonempty
        (K23RouteCoverageData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)) \/
        Nonempty
          (ThreeCommonNeighborRouteCoverageData.{u}
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8)) \/
          Nonempty
            (CommonNeighborRouteCoverageData.{u}
              (payForCut := payForCut) (topologyArc := topologyArc)
              (lemma8 := lemma8)) \/
            Nonempty
              (LocalExclusionRouteCoverageData.{u}
                (payForCut := payForCut) (topologyArc := topologyArc)
                (lemma8 := lemma8)) :=
  NoEarlyConcreteSourceFamilyW29.nonempty_routeData_iff
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem routeData_nonempty_iff_routeCoverage :
    Nonempty
        (ConcreteNoEarlyRouteData.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)) <->
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) := by
  constructor
  case mp =>
    intro hroute
    have hsplit :=
      (routeData_nonempty_iff_routeCoverageData
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp hroute
    cases hsplit with
    | inl hK23 =>
        exact Or.inl
          ((nonempty_k23RouteCoverageData_iff
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8)).mp hK23)
    | inr hRest =>
        cases hRest with
        | inl hThree =>
            exact Or.inr (Or.inl
              ((nonempty_threeCommonNeighborRouteCoverageData_iff
                (payForCut := payForCut) (topologyArc := topologyArc)
                (lemma8 := lemma8)).mp hThree))
        | inr hRest2 =>
            cases hRest2 with
            | inl hCommon =>
                exact Or.inr (Or.inr (Or.inl
                  ((nonempty_commonNeighborRouteCoverageData_iff
                    (payForCut := payForCut) (topologyArc := topologyArc)
                    (lemma8 := lemma8)).mp hCommon)))
            | inr hLocal =>
                exact Or.inr (Or.inr (Or.inr
                  ((nonempty_localExclusionRouteCoverageData_iff
                    (payForCut := payForCut) (topologyArc := topologyArc)
                    (lemma8 := lemma8)).mp hLocal)))
  case mpr =>
    intro hcoverage
    apply
      (routeData_nonempty_iff_routeCoverageData
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr
    cases hcoverage with
    | inl hK23 =>
        exact Or.inl
          ((nonempty_k23RouteCoverageData_iff
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8)).mpr hK23)
    | inr hRest =>
        cases hRest with
        | inl hThree =>
            exact Or.inr (Or.inl
              ((nonempty_threeCommonNeighborRouteCoverageData_iff
                (payForCut := payForCut) (topologyArc := topologyArc)
                (lemma8 := lemma8)).mpr hThree))
        | inr hRest2 =>
            cases hRest2 with
            | inl hCommon =>
                exact Or.inr (Or.inr (Or.inl
                  ((nonempty_commonNeighborRouteCoverageData_iff
                    (payForCut := payForCut) (topologyArc := topologyArc)
                    (lemma8 := lemma8)).mpr hCommon)))
            | inr hLocal =>
                exact Or.inr (Or.inr (Or.inr
                  ((nonempty_localExclusionRouteCoverageData_iff
                    (payForCut := payForCut) (topologyArc := topologyArc)
                    (lemma8 := lemma8)).mpr hLocal)))

theorem nonempty_routeData_of_routeCoverage
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Nonempty
      (ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :=
  (routeData_nonempty_iff_routeCoverage
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)).2 h

def routeDataOfRouteCoverageAvailable
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    ConcreteNoEarlyRouteData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  Classical.choice
    (nonempty_routeData_of_routeCoverage
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h)

theorem nonempty_coverageFamily_of_routeCoverage
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Nonempty
      (NoEarlyCoverageFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) := by
  cases h with
  | inl hK23 =>
      exact hK23.1
  | inr hRest =>
      cases hRest with
      | inl hThree =>
          exact hThree.1
      | inr hRest2 =>
          cases hRest2 with
          | inl hCommon =>
              exact hCommon.1
          | inr hLocal =>
              exact hLocal.1

def coverageFamilyOfRouteCoverageAvailable
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    NoEarlyCoverageFamily.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  coverageFamilyOfRouteData
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)
    (routeDataOfRouteCoverageAvailable
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h)

def coverageRowOfRouteCoverageAvailable
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    M8Lemma9NoEarlyCoverageRow payForCut topologyArc lemma8 C hmin :=
  (coverageFamilyOfRouteCoverageAvailable
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) h).row C hmin

def gapNegativeCoverageDataOfRouteCoverageAvailable
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Lemma6Lemma7AssemblyW13.GapNegativeCoverageData
      (RowBoundary payForCut topologyArc lemma8 C hmin)
      ((coverageRowOfRouteCoverageAvailable
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) h C hmin).longArcCount) :=
  (coverageRowOfRouteCoverageAvailable
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) h C hmin).coverage

def lemma9SourceFieldsOfRouteCoverageAvailable
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  lemma9SourceFieldsOfRouteData
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)
    (routeDataOfRouteCoverageAvailable
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h)
    C hmin

def natLateTripleInputsOfRouteCoverageAvailable
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    LateTriplesInterface.M8NatLateTripleInputs
      (Lemma9ProducerFamilyW20.AssembledLemma9PreLateBase
        payForCut topologyArc lemma8 C hmin).localLabels.predicates.data :=
  (lemma9SourceFieldsOfRouteCoverageAvailable
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) h C hmin).natLateTripleInputs

def lemma9SourceFamilyOfRouteCoverageAvailable
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  lemma9SourceFamilyOfRouteData
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)
    (routeDataOfRouteCoverageAvailable
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h)

theorem nonempty_lemma9SourceFields_of_routeCoverage
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (SourceFields payForCut topologyArc lemma8 C hmin) :=
  Nonempty.intro
    (lemma9SourceFieldsOfRouteCoverageAvailable
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h C hmin)

def concreteNoEarlySourceFamilyOfRouteCoverageAvailable
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    M8ConcreteNoEarlySourceFamily.{u} payForCut topologyArc lemma8 :=
  (routeDataOfRouteCoverageAvailable
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) h).toConcreteNoEarlySourceFamily

theorem nonempty_concreteNoEarlySourceFamily_of_routeCoverage
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Nonempty
      (M8ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro
    (concreteNoEarlySourceFamilyOfRouteCoverageAvailable
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) h)

/-- Route coverage supplies the exact concrete five-start no-early equality
for any assembled minimal-failure row. -/
def concreteNoEarlyTripleEqualityOfRouteCoverageAvailable
    (h :
      NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    NoEarlyTripleConcrete.M8ConcreteNoEarlyTripleEquality
      (RowPredicates payForCut topologyArc lemma8 C hmin) :=
  let F := concreteNoEarlySourceFamilyOfRouteCoverageAvailable
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) h
  (F.row C hmin).obstruction.toConcreteNoEarlyTripleEquality

theorem routeCoverage_iff_w31_coverage_and_obstructionRoute :
    NoEarlyRouteCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) <->
      NoEarlyCoverageAvailable.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8) /\
        NoEarlyObstructionRouteAvailable.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | inl hK23 =>
        exact And.intro hK23.1 (Or.inl hK23.2)
    | inr hRest =>
        cases hRest with
        | inl hThree =>
            exact And.intro hThree.1 (Or.inr (Or.inl hThree.2))
        | inr hRest2 =>
            cases hRest2 with
            | inl hCommon =>
                exact And.intro hCommon.1
                  (Or.inr (Or.inr (Or.inl hCommon.2)))
            | inr hLocal =>
                exact And.intro hLocal.1
                  (Or.inr (Or.inr (Or.inr hLocal.2)))
  case mpr =>
    intro h
    cases h.2 with
    | inl hK23 =>
        exact Or.inl (And.intro h.1 hK23)
    | inr hRest =>
        cases hRest with
        | inl hThree =>
            exact Or.inr (Or.inl (And.intro h.1 hThree))
        | inr hRest2 =>
            cases hRest2 with
            | inl hCommon =>
                exact Or.inr (Or.inr (Or.inl
                  (And.intro h.1 hCommon)))
            | inr hLocal =>
                exact Or.inr (Or.inr (Or.inr
                  (And.intro h.1 hLocal)))

/-- If only coverage has been produced, the exact remaining field needed for
the no-early equality is the W31 obstruction-route sum. -/
def concreteNoEarlyTripleEqualityOfCoverageAndObstructionRoute
    (hcoverage :
      NoEarlyCoverageAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    (hobstruction :
      NoEarlyObstructionRouteAvailable.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    NoEarlyTripleConcrete.M8ConcreteNoEarlyTripleEquality
      (RowPredicates payForCut topologyArc lemma8 C hmin) :=
  concreteNoEarlyTripleEqualityOfRouteCoverageAvailable
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)
    ((routeCoverage_iff_w31_coverage_and_obstructionRoute
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8)).2 (And.intro hcoverage hobstruction))
    C hmin

/-! ## Exact missing route coverage blockers -/

theorem not_routeCoverage_iff_exactBlockers :
    Not
        (NoEarlyRouteCoverageAvailable.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)) <->
      ExactNoEarlyRouteCoverageBlockers.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) := by
  constructor
  case mp =>
    intro hbad
    constructor
    case left =>
      intro hK23
      exact hbad (Or.inl hK23)
    case right =>
      constructor
      case left =>
        intro hThree
        exact hbad (Or.inr (Or.inl hThree))
      case right =>
        constructor
        case left =>
          intro hCommon
          exact hbad (Or.inr (Or.inr (Or.inl hCommon)))
        case right =>
          intro hLocal
          exact hbad (Or.inr (Or.inr (Or.inr hLocal)))
  case mpr =>
    intro hbad hroute
    cases hroute with
    | inl hK23 =>
        exact hbad.1 hK23
    | inr hRest =>
        cases hRest with
        | inl hThree =>
            exact hbad.2.1 hThree
        | inr hRest2 =>
            cases hRest2 with
            | inl hCommon =>
                exact hbad.2.2.1 hCommon
            | inr hLocal =>
                exact hbad.2.2.2 hLocal

theorem exactRouteCoverageBlockers_iff_individualRouteBlockers :
    ExactNoEarlyRouteCoverageBlockers.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) <->
      ExactK23RouteCoverageBlocker.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8) /\
        ExactThreeCommonNeighborRouteCoverageBlocker.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8) /\
          ExactCommonNeighborRouteCoverageBlocker.{u}
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8) /\
            ExactLocalExclusionRouteCoverageBlocker.{u}
              (payForCut := payForCut) (topologyArc := topologyArc)
              (lemma8 := lemma8) := by
  constructor
  case mp =>
    intro hbad
    exact
      And.intro
        ((not_k23_routeCoverage_iff_exactK23RouteCoverageBlocker
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)).mp hbad.1)
        (And.intro
          ((not_threeCommonNeighbor_routeCoverage_iff_exactThreeCommonNeighborRouteCoverageBlocker
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8)).mp hbad.2.1)
          (And.intro
            ((not_commonNeighbor_routeCoverage_iff_exactCommonNeighborRouteCoverageBlocker
              (payForCut := payForCut) (topologyArc := topologyArc)
              (lemma8 := lemma8)).mp hbad.2.2.1)
            ((not_localExclusion_routeCoverage_iff_exactLocalExclusionRouteCoverageBlocker
              (payForCut := payForCut) (topologyArc := topologyArc)
              (lemma8 := lemma8)).mp hbad.2.2.2)))
  case mpr =>
    intro hbad
    exact
      And.intro
        ((not_k23_routeCoverage_iff_exactK23RouteCoverageBlocker
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)).mpr hbad.1)
        (And.intro
          ((not_threeCommonNeighbor_routeCoverage_iff_exactThreeCommonNeighborRouteCoverageBlocker
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8)).mpr hbad.2.1)
          (And.intro
            ((not_commonNeighbor_routeCoverage_iff_exactCommonNeighborRouteCoverageBlocker
              (payForCut := payForCut) (topologyArc := topologyArc)
              (lemma8 := lemma8)).mpr hbad.2.2.1)
            ((not_localExclusion_routeCoverage_iff_exactLocalExclusionRouteCoverageBlocker
              (payForCut := payForCut) (topologyArc := topologyArc)
              (lemma8 := lemma8)).mpr hbad.2.2.2)))

theorem noRouteData_iff_exactRouteCoverageBlockers :
    Not
        (Nonempty
          (ConcreteNoEarlyRouteData.{u}
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8))) <->
      ExactNoEarlyRouteCoverageBlockers.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) := by
  constructor
  case mp =>
    intro hbad
    exact
      (not_routeCoverage_iff_exactBlockers
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp
        (fun hcoverage =>
          hbad
            ((routeData_nonempty_iff_routeCoverage
              (payForCut := payForCut) (topologyArc := topologyArc)
              (lemma8 := lemma8)).mpr hcoverage))
  case mpr =>
    intro hbad hroute
    exact
      ((not_routeCoverage_iff_exactBlockers
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr hbad)
        ((routeData_nonempty_iff_routeCoverage
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)).mp hroute)

theorem exactMissingNoEarlyRouteBlocker_iff_exactRouteCoverageBlockers :
    ExactMissingNoEarlyRouteBlocker.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) <->
      ExactNoEarlyRouteCoverageBlockers.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) :=
  Iff.trans
    (NoEarlyConcreteRowsW31.exactMissingNoEarlyRouteBlocker_iff_not_routeData
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))
    (noRouteData_iff_exactRouteCoverageBlockers
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))

theorem exactRouteCoverageBlockers_iff_missingCoverage_or_allObstructions :
    ExactNoEarlyRouteCoverageBlockers.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) <->
      Not
        (Nonempty
          (NoEarlyCoverageFamily.{u}
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8))) \/
        AllNoEarlyObstructionRoutesMissing.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8) :=
  Iff.trans
    (noRouteData_iff_exactRouteCoverageBlockers
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8)).symm
    (NoEarlyConcreteRowsW31.not_routeData_iff_missingCoverage_or_allObstructionRoutesMissing
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))

end NoEarlyRouteCoverageClosureW32
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW32ConcreteNoEarlyRouteData
    (payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) :=
  Swanepoel.NoEarlyRouteCoverageClosureW32.ConcreteNoEarlyRouteData.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

abbrev SwanepoelW32NoEarlyRouteCoverageAvailable
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} : Prop :=
  Swanepoel.NoEarlyRouteCoverageClosureW32.NoEarlyRouteCoverageAvailable.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

abbrev SwanepoelW32ExactNoEarlyRouteCoverageBlockers
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} : Prop :=
  Swanepoel.NoEarlyRouteCoverageClosureW32.ExactNoEarlyRouteCoverageBlockers.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem swanepoelW32_routeData_iff_routeCoverage
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    Nonempty
        (SwanepoelW32ConcreteNoEarlyRouteData
          payForCut topologyArc lemma8) <->
      SwanepoelW32NoEarlyRouteCoverageAvailable
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) :=
  Swanepoel.NoEarlyRouteCoverageClosureW32.routeData_nonempty_iff_routeCoverage
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem swanepoelW32_noRouteData_iff_exactRouteCoverageBlockers
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    Not
        (Nonempty
          (SwanepoelW32ConcreteNoEarlyRouteData
            payForCut topologyArc lemma8)) <->
      SwanepoelW32ExactNoEarlyRouteCoverageBlockers
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) :=
  Swanepoel.NoEarlyRouteCoverageClosureW32.noRouteData_iff_exactRouteCoverageBlockers
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem swanepoelW32_exactMissingBlocker_iff_exactRouteCoverageBlockers
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    Swanepoel.NoEarlyConcreteRowsW31.ExactMissingNoEarlyRouteBlocker.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) <->
      SwanepoelW32ExactNoEarlyRouteCoverageBlockers
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8) :=
  Swanepoel.NoEarlyRouteCoverageClosureW32.exactMissingNoEarlyRouteBlocker_iff_exactRouteCoverageBlockers
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

end Verified
end ErdosProblems1066

end
