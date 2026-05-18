import ErdosProblems1066.Swanepoel.NoEarlyRouteDataClosureW30

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W31 no-early concrete rows

This worker is a leaf over W30.  It gives direct row and source-family
constructors from the W27 coverage and obstruction families, and names the
exact route-data blocker left after the W30 split.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyConcreteRowsW31

open Lemma9NoEarlyConstructionW26
open Lemma9NoEarlyObstructionInhabitationW25
open Lemma9NoEarlySourceRowsW28
open Lemma9ProducerFamilyW20
open Lemma9SourceFamilyConcreteW27
open MinimalGraphFacts
open NoEarlyConcreteSourceFamilyW29
open NoEarlyRouteDataClosureW30

universe u

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}
variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-! ## Row constructors from coverage plus one obstruction family -/

def k23SourceRowOfCoverageAndObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8K23ObstructionRowFamily.{u} payForCut topologyArc lemma8)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    M8K23NoEarlySourceRow payForCut topologyArc lemma8 C hmin :=
  (coverage.row C hmin).toW26K23SourceRow
    (obstruction.row C hmin)

def threeCommonNeighborSourceRowOfCoverageAndObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8ThreeCommonNeighborObstructionRowFamily.{u}
        payForCut topologyArc lemma8)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    M8ThreeCommonNeighborNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin :=
  (coverage.row C hmin).toW26ThreeCommonNeighborSourceRow
    (obstruction.row C hmin)

def commonNeighborSourceRowOfCoverageAndObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8CommonNeighborCardObstructionRowFamily.{u}
        payForCut topologyArc lemma8)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    M8CommonNeighborNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin :=
  (coverage.row C hmin).toW26CommonNeighborSourceRow
    (obstruction.row C hmin)

def concreteSourceRowOfCoverageAndK23Obstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8K23ObstructionRowFamily.{u} payForCut topologyArc lemma8)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    M8ConcreteNoEarlySourceRow payForCut topologyArc lemma8 C hmin :=
  (k23SourceRowOfCoverageAndObstruction
    coverage obstruction C hmin).toW25SourceRow

def concreteSourceRowOfCoverageAndThreeCommonNeighborObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8ThreeCommonNeighborObstructionRowFamily.{u}
        payForCut topologyArc lemma8)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    M8ConcreteNoEarlySourceRow payForCut topologyArc lemma8 C hmin :=
  (threeCommonNeighborSourceRowOfCoverageAndObstruction
    coverage obstruction C hmin).toW25SourceRow

def concreteSourceRowOfCoverageAndCommonNeighborObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8CommonNeighborCardObstructionRowFamily.{u}
        payForCut topologyArc lemma8)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    M8ConcreteNoEarlySourceRow payForCut topologyArc lemma8 C hmin :=
  (commonNeighborSourceRowOfCoverageAndObstruction
    coverage obstruction C hmin).toW25SourceRow

def concreteSourceRowOfCoverageAndLocalExclusionObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8LocalExclusionObstructionPackageFamily.{u}
        payForCut topologyArc lemma8)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    M8ConcreteNoEarlySourceRow payForCut topologyArc lemma8 C hmin :=
  (coverage.row C hmin).toW25SourceRowOfObstructionPackage
    (obstruction.row C hmin)

def sourceFieldsOfCoverageAndK23Obstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8K23ObstructionRowFamily.{u} payForCut topologyArc lemma8)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  (concreteSourceRowOfCoverageAndK23Obstruction
    coverage obstruction C hmin).toSourceFields

def sourceFieldsOfCoverageAndThreeCommonNeighborObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8ThreeCommonNeighborObstructionRowFamily.{u}
        payForCut topologyArc lemma8)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  (concreteSourceRowOfCoverageAndThreeCommonNeighborObstruction
    coverage obstruction C hmin).toSourceFields

def sourceFieldsOfCoverageAndCommonNeighborObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8CommonNeighborCardObstructionRowFamily.{u}
        payForCut topologyArc lemma8)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  (concreteSourceRowOfCoverageAndCommonNeighborObstruction
    coverage obstruction C hmin).toSourceFields

def sourceFieldsOfCoverageAndLocalExclusionObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8LocalExclusionObstructionPackageFamily.{u}
        payForCut topologyArc lemma8)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  (concreteSourceRowOfCoverageAndLocalExclusionObstruction
    coverage obstruction C hmin).toSourceFields

/-! ## Family constructors from coverage plus one obstruction family -/

def k23SourceFamilyOfCoverageAndObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8K23ObstructionRowFamily.{u} payForCut topologyArc lemma8) :
    M8K23NoEarlySourceFamily.{u} payForCut topologyArc lemma8 where
  row := fun C hmin =>
    k23SourceRowOfCoverageAndObstruction coverage obstruction C hmin

def threeCommonNeighborSourceFamilyOfCoverageAndObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8ThreeCommonNeighborObstructionRowFamily.{u}
        payForCut topologyArc lemma8) :
    M8ThreeCommonNeighborNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    threeCommonNeighborSourceRowOfCoverageAndObstruction
      coverage obstruction C hmin

def commonNeighborSourceFamilyOfCoverageAndObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8CommonNeighborCardObstructionRowFamily.{u}
        payForCut topologyArc lemma8) :
    M8CommonNeighborNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    commonNeighborSourceRowOfCoverageAndObstruction
      coverage obstruction C hmin

def concreteSourceFamilyOfCoverageAndK23Obstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8K23ObstructionRowFamily.{u} payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u} payForCut topologyArc lemma8 where
  row := fun C hmin =>
    concreteSourceRowOfCoverageAndK23Obstruction
      coverage obstruction C hmin

def concreteSourceFamilyOfCoverageAndThreeCommonNeighborObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8ThreeCommonNeighborObstructionRowFamily.{u}
        payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u} payForCut topologyArc lemma8 where
  row := fun C hmin =>
    concreteSourceRowOfCoverageAndThreeCommonNeighborObstruction
      coverage obstruction C hmin

def concreteSourceFamilyOfCoverageAndCommonNeighborObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8CommonNeighborCardObstructionRowFamily.{u}
        payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u} payForCut topologyArc lemma8 where
  row := fun C hmin =>
    concreteSourceRowOfCoverageAndCommonNeighborObstruction
      coverage obstruction C hmin

def concreteSourceFamilyOfCoverageAndLocalExclusionObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8LocalExclusionObstructionPackageFamily.{u}
        payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u} payForCut topologyArc lemma8 where
  row := fun C hmin =>
    concreteSourceRowOfCoverageAndLocalExclusionObstruction
      coverage obstruction C hmin

def sourceFamilyOfCoverageAndK23Obstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8K23ObstructionRowFamily.{u} payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u} payForCut topologyArc lemma8 :=
  (concreteSourceFamilyOfCoverageAndK23Obstruction
    coverage obstruction).toSourceFamily

def sourceFamilyOfCoverageAndThreeCommonNeighborObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8ThreeCommonNeighborObstructionRowFamily.{u}
        payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u} payForCut topologyArc lemma8 :=
  (concreteSourceFamilyOfCoverageAndThreeCommonNeighborObstruction
    coverage obstruction).toSourceFamily

def sourceFamilyOfCoverageAndCommonNeighborObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8CommonNeighborCardObstructionRowFamily.{u}
        payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u} payForCut topologyArc lemma8 :=
  (concreteSourceFamilyOfCoverageAndCommonNeighborObstruction
    coverage obstruction).toSourceFamily

def sourceFamilyOfCoverageAndLocalExclusionObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8LocalExclusionObstructionPackageFamily.{u}
        payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u} payForCut topologyArc lemma8 :=
  (concreteSourceFamilyOfCoverageAndLocalExclusionObstruction
    coverage obstruction).toSourceFamily

/-! ## Rows and source fields from W30 route data -/

def concreteSourceRowOfRouteData
    (D :
      M8ConcreteNoEarlySourceRouteData.{u}
        payForCut topologyArc lemma8)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    M8ConcreteNoEarlySourceRow payForCut topologyArc lemma8 C hmin :=
  D.toConcreteNoEarlySourceFamily.row C hmin

def sourceFieldsOfRouteData
    (D :
      M8ConcreteNoEarlySourceRouteData.{u}
        payForCut topologyArc lemma8)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  (concreteSourceRowOfRouteData D C hmin).toSourceFields

def sourceFamilyOfRouteData
    (D :
      M8ConcreteNoEarlySourceRouteData.{u}
        payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  D.toConcreteNoEarlySourceFamily.toSourceFamily

theorem nonempty_sourceFamily_of_coverage_and_k23Obstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8K23ObstructionRowFamily.{u} payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro
    (sourceFamilyOfCoverageAndK23Obstruction coverage obstruction)

theorem nonempty_sourceFamily_of_coverage_and_threeCommonNeighborObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8ThreeCommonNeighborObstructionRowFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro
    (sourceFamilyOfCoverageAndThreeCommonNeighborObstruction
      coverage obstruction)

theorem nonempty_sourceFamily_of_coverage_and_commonNeighborObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8CommonNeighborCardObstructionRowFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro
    (sourceFamilyOfCoverageAndCommonNeighborObstruction
      coverage obstruction)

theorem nonempty_sourceFamily_of_coverage_and_localExclusionObstruction
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (obstruction :
      M8LocalExclusionObstructionPackageFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro
    (sourceFamilyOfCoverageAndLocalExclusionObstruction
      coverage obstruction)

/-! ## Exact missing route blockers -/

abbrev NoEarlyCoverageAvailable : Prop :=
  Nonempty
    (M8Lemma9NoEarlyCoverageFamily.{u}
      payForCut topologyArc lemma8)

abbrev NoEarlyObstructionRouteAvailable : Prop :=
  Nonempty
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
      payForCut topologyArc lemma8)

abbrev ExactMissingNoEarlyRouteBlocker : Prop :=
  Not (NoEarlyCoverageAvailable.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) /\
    NoEarlyObstructionRouteAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))

abbrev AllNoEarlyObstructionRoutesMissing : Prop :=
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
        payForCut topologyArc lemma8))

theorem exactMissingNoEarlyRouteBlocker_iff_not_routeData :
    ExactMissingNoEarlyRouteBlocker.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) <->
      Not
        (Nonempty
          (M8ConcreteNoEarlySourceRouteData.{u}
            payForCut topologyArc lemma8)) := by
  constructor
  case mp =>
    intro hmissing hroute
    exact hmissing
      ((nonempty_routeData_iff_coverage_and_obstruction
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp hroute)
  case mpr =>
    intro hroute hcomponents
    exact hroute
      ((nonempty_routeData_iff_coverage_and_obstruction
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mpr hcomponents)

theorem noRouteData_of_missingCoverage
    (hcoverage :
      Not
        (Nonempty
          (M8Lemma9NoEarlyCoverageFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8ConcreteNoEarlySourceRouteData.{u}
          payForCut topologyArc lemma8)) := by
  intro hroute
  exact hcoverage
    (((nonempty_routeData_iff_coverage_and_obstruction
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8)).mp hroute).1)

theorem noRouteData_of_allObstructionRoutesMissing
    (hmissing :
      AllNoEarlyObstructionRoutesMissing.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    Not
      (Nonempty
        (M8ConcreteNoEarlySourceRouteData.{u}
          payForCut topologyArc lemma8)) := by
  intro hroute
  have hcomponents :=
    (nonempty_routeData_iff_coverage_and_obstruction
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8)).mp hroute
  cases hcomponents.2 with
  | inl hK23 =>
      exact hmissing.1 hK23
  | inr hRest =>
      cases hRest with
      | inl hThree =>
          exact hmissing.2.1 hThree
      | inr hRest2 =>
          cases hRest2 with
          | inl hCommon =>
              exact hmissing.2.2.1 hCommon
          | inr hLocal =>
              exact hmissing.2.2.2 hLocal

theorem allObstructionRoutesMissing_of_noRouteData_and_coverage
    (hroute :
      Not
        (Nonempty
          (M8ConcreteNoEarlySourceRouteData.{u}
            payForCut topologyArc lemma8)))
    (hcoverage :
      Nonempty
        (M8Lemma9NoEarlyCoverageFamily.{u}
          payForCut topologyArc lemma8)) :
    AllNoEarlyObstructionRoutesMissing.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  not_each_obstruction_of_not_routeData_and_coverage
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) hroute hcoverage

theorem not_routeData_iff_missingCoverage_or_allObstructionRoutesMissing :
    Not
      (Nonempty
        (M8ConcreteNoEarlySourceRouteData.{u}
          payForCut topologyArc lemma8)) <->
      Not
        (Nonempty
          (M8Lemma9NoEarlyCoverageFamily.{u}
            payForCut topologyArc lemma8)) \/
        AllNoEarlyObstructionRoutesMissing.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8) := by
  classical
  constructor
  case mp =>
    intro hroute
    by_cases hcoverage :
        Nonempty
          (M8Lemma9NoEarlyCoverageFamily.{u}
            payForCut topologyArc lemma8)
    · exact Or.inr
        (allObstructionRoutesMissing_of_noRouteData_and_coverage
          hroute hcoverage)
    · exact Or.inl hcoverage
  case mpr =>
    intro hmissing
    cases hmissing with
    | inl hcoverage =>
        exact noRouteData_of_missingCoverage hcoverage
    | inr hobstructions =>
        exact noRouteData_of_allObstructionRoutesMissing hobstructions

end NoEarlyConcreteRowsW31
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW31ConcreteNoEarlySourceRouteData
    (payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) :=
  Swanepoel.NoEarlyConcreteSourceFamilyW29.M8ConcreteNoEarlySourceRouteData.{u}
    payForCut topologyArc lemma8

abbrev SwanepoelW31ExactMissingNoEarlyRouteBlocker
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} : Prop :=
  Swanepoel.NoEarlyConcreteRowsW31.ExactMissingNoEarlyRouteBlocker.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

abbrev SwanepoelW31AllNoEarlyObstructionRoutesMissing
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} : Prop :=
  Swanepoel.NoEarlyConcreteRowsW31.AllNoEarlyObstructionRoutesMissing.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem swanepoelW31_exactMissingNoEarlyRouteBlocker_iff_not_routeData
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    SwanepoelW31ExactMissingNoEarlyRouteBlocker
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) <->
      Not
        (Nonempty
          (SwanepoelW31ConcreteNoEarlySourceRouteData
            payForCut topologyArc lemma8)) :=
  Swanepoel.NoEarlyConcreteRowsW31.exactMissingNoEarlyRouteBlocker_iff_not_routeData
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem swanepoelW31_notRouteData_iff_missingCoverage_or_allObstructionsMissing
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    Not
      (Nonempty
        (SwanepoelW31ConcreteNoEarlySourceRouteData
          payForCut topologyArc lemma8)) <->
      Not
        (Nonempty
          (Swanepoel.Lemma9SourceFamilyConcreteW27.M8Lemma9NoEarlyCoverageFamily.{u}
            payForCut topologyArc lemma8)) \/
        SwanepoelW31AllNoEarlyObstructionRoutesMissing
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8) :=
  Swanepoel.NoEarlyConcreteRowsW31.not_routeData_iff_missingCoverage_or_allObstructionRoutesMissing
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

end Verified
end ErdosProblems1066

end
