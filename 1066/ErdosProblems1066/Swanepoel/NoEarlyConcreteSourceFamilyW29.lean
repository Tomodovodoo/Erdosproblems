import ErdosProblems1066.Swanepoel.Lemma9NoEarlySourceRowsW28

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W29 concrete no-early source-family routes

This worker keeps the Lemma 9 no-early source-family construction on concrete
row data.  K23, three-common-neighbor, and common-neighbor-card rows are first
packaged as local-exclusion/no-early rows using the finite local exclusions
available for minimal failures; the resulting rows then inhabit the existing
W25 `M8ConcreteNoEarlySourceFamily`.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyConcreteSourceFamilyW29

open LateTriplesInterface
open Lemma10Bridge
open Lemma6Lemma7AssemblyW13
open Lemma9NoEarlyConstructionW26
open Lemma9NoEarlyInhabitationW24
open Lemma9NoEarlyObstructionInhabitationW25
open Lemma9NoEarlySourceRowsW28
open Lemma9ProducerFamilyW20
open Lemma9SourceFamilyConcreteW27
open LocalConfigurations
open MinimalFailureLocalExclusions
open MinimalGraphFacts
open NoEarlyTripleObstructionConcrete

universe u

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}
variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-! ## Row-level local-exclusion packages -/

def finiteLocalExclusionsOfMinimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) :
    FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C) :=
  K23ObstructionConcrete.finiteLocalExclusionPackage_of_minimalFailure_noAssumptions
    hmin

def localExclusionPackageOfK23Row
    (H :
      M8ConcreteK23ObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    M8ConcreteNoEarlyObstructionPackage
      (RowPredicates payForCut topologyArc lemma8 C hmin) :=
  M8ConcreteNoEarlyObstructionPackage.k23 H
    (finiteLocalExclusionsOfMinimalFailure hmin)

def localExclusionPackageOfThreeCommonNeighborRow
    (H :
      K23ObstructionConcrete.M8ConcreteThreeCommonNeighborObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    M8ConcreteNoEarlyObstructionPackage
      (RowPredicates payForCut topologyArc lemma8 C hmin) :=
  M8ConcreteNoEarlyObstructionPackage.k23 H.toK23ObstructionInputs
    (finiteLocalExclusionsOfMinimalFailure hmin)

def localExclusionPackageOfCommonNeighborRow
    (H :
      K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    M8ConcreteNoEarlyObstructionPackage
      (RowPredicates payForCut topologyArc lemma8 C hmin) :=
  M8ConcreteNoEarlyObstructionPackage.commonNeighbor H
    (finiteLocalExclusionsOfMinimalFailure hmin)

def concreteNoEarlySourceRowOfCoverageAndK23
    (R : M8Lemma9NoEarlyCoverageRow
      payForCut topologyArc lemma8 C hmin)
    (H :
      M8ConcreteK23ObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    M8ConcreteNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin :=
  R.toW25SourceRowOfObstructionPackage
    (localExclusionPackageOfK23Row H)

def concreteNoEarlySourceRowOfCoverageAndThreeCommonNeighbor
    (R : M8Lemma9NoEarlyCoverageRow
      payForCut topologyArc lemma8 C hmin)
    (H :
      K23ObstructionConcrete.M8ConcreteThreeCommonNeighborObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    M8ConcreteNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin :=
  R.toW25SourceRowOfObstructionPackage
    (localExclusionPackageOfThreeCommonNeighborRow H)

def concreteNoEarlySourceRowOfCoverageAndCommonNeighbor
    (R : M8Lemma9NoEarlyCoverageRow
      payForCut topologyArc lemma8 C hmin)
    (H :
      K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    M8ConcreteNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin :=
  R.toW25SourceRowOfObstructionPackage
    (localExclusionPackageOfCommonNeighborRow H)

/-! ## Family-level concrete source constructors -/

def finiteLocalExclusionFamilyOfMinimalFailures :
    M8FiniteLocalExclusionFamily.{u} :=
  M8FiniteLocalExclusionFamily.ofMinimalFailures

def localExclusionDataOfK23Data
    (D : M8K23NoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8 :=
  localExclusionSourceFamilyDataOfK23
    D.coverage D.obstruction finiteLocalExclusionFamilyOfMinimalFailures

def localExclusionDataOfThreeCommonNeighborData
    (D : M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8 :=
  localExclusionSourceFamilyDataOfThreeCommonNeighbor
    D.coverage D.obstruction finiteLocalExclusionFamilyOfMinimalFailures

def localExclusionDataOfCommonNeighborData
    (D : M8CommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8 :=
  localExclusionSourceFamilyDataOfCommonNeighbor
    D.coverage D.obstruction finiteLocalExclusionFamilyOfMinimalFailures

def concreteNoEarlySourceFamilyOfK23Data
    (D : M8K23NoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 :=
  (localExclusionDataOfK23Data D).toW25SourceFamily

def concreteNoEarlySourceFamilyOfThreeCommonNeighborData
    (D : M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 :=
  (localExclusionDataOfThreeCommonNeighborData D).toW25SourceFamily

def concreteNoEarlySourceFamilyOfCommonNeighborData
    (D : M8CommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 :=
  (localExclusionDataOfCommonNeighborData D).toW25SourceFamily

def concreteNoEarlySourceFamilyOfLocalExclusionData
    (D : M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 :=
  D.toW25SourceFamily

/-! ## Concrete route data and exact blockers -/

inductive M8ConcreteNoEarlySourceRouteData
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  | k23 :
      M8K23NoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8 ->
      M8ConcreteNoEarlySourceRouteData payForCut topologyArc lemma8
  | threeCommonNeighbor :
      M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8 ->
      M8ConcreteNoEarlySourceRouteData payForCut topologyArc lemma8
  | commonNeighbor :
      M8CommonNeighborNoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8 ->
      M8ConcreteNoEarlySourceRouteData payForCut topologyArc lemma8
  | localExclusion :
      M8LocalExclusionNoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8 ->
      M8ConcreteNoEarlySourceRouteData payForCut topologyArc lemma8

namespace M8ConcreteNoEarlySourceRouteData

def toLocalExclusionData
    (D : M8ConcreteNoEarlySourceRouteData.{u}
      payForCut topologyArc lemma8) :
    M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8 :=
  match D with
  | M8ConcreteNoEarlySourceRouteData.k23 K =>
      localExclusionDataOfK23Data K
  | M8ConcreteNoEarlySourceRouteData.threeCommonNeighbor K =>
      localExclusionDataOfThreeCommonNeighborData K
  | M8ConcreteNoEarlySourceRouteData.commonNeighbor K =>
      localExclusionDataOfCommonNeighborData K
  | M8ConcreteNoEarlySourceRouteData.localExclusion K =>
      K

def toConcreteNoEarlySourceFamily
    (D : M8ConcreteNoEarlySourceRouteData.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 :=
  D.toLocalExclusionData.toW25SourceFamily

theorem nonempty_localExclusionData
    (D : M8ConcreteNoEarlySourceRouteData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (M8LocalExclusionNoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toLocalExclusionData

theorem nonempty_concreteNoEarlySourceFamily
    (D : M8ConcreteNoEarlySourceRouteData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (M8ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toConcreteNoEarlySourceFamily

end M8ConcreteNoEarlySourceRouteData

def routeDataOfK23Data
    (D : M8K23NoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceRouteData.{u}
      payForCut topologyArc lemma8 :=
  M8ConcreteNoEarlySourceRouteData.k23 D

def routeDataOfThreeCommonNeighborData
    (D : M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceRouteData.{u}
      payForCut topologyArc lemma8 :=
  M8ConcreteNoEarlySourceRouteData.threeCommonNeighbor D

def routeDataOfCommonNeighborData
    (D : M8CommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceRouteData.{u}
      payForCut topologyArc lemma8 :=
  M8ConcreteNoEarlySourceRouteData.commonNeighbor D

def routeDataOfLocalExclusionData
    (D : M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceRouteData.{u}
      payForCut topologyArc lemma8 :=
  M8ConcreteNoEarlySourceRouteData.localExclusion D

theorem nonempty_concreteNoEarlySourceFamily_of_k23Data
    (h :
      Nonempty
        (M8K23NoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (M8ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h with
  | intro D =>
      exact Nonempty.intro (concreteNoEarlySourceFamilyOfK23Data D)

theorem nonempty_concreteNoEarlySourceFamily_of_threeCommonNeighborData
    (h :
      Nonempty
        (M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (M8ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h with
  | intro D =>
      exact Nonempty.intro
        (concreteNoEarlySourceFamilyOfThreeCommonNeighborData D)

theorem nonempty_concreteNoEarlySourceFamily_of_commonNeighborData
    (h :
      Nonempty
        (M8CommonNeighborNoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (M8ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h with
  | intro D =>
      exact Nonempty.intro
        (concreteNoEarlySourceFamilyOfCommonNeighborData D)

theorem nonempty_concreteNoEarlySourceFamily_of_localExclusionData
    (h :
      Nonempty
        (M8LocalExclusionNoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (M8ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h with
  | intro D =>
      exact Nonempty.intro
        (concreteNoEarlySourceFamilyOfLocalExclusionData D)

theorem nonempty_concreteNoEarlySourceFamily_of_routeData
    (h :
      Nonempty
        (M8ConcreteNoEarlySourceRouteData.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (M8ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h with
  | intro D =>
      exact D.nonempty_concreteNoEarlySourceFamily

theorem nonempty_routeData_iff :
    Nonempty
      (M8ConcreteNoEarlySourceRouteData.{u}
        payForCut topologyArc lemma8) <->
      Nonempty
        (M8K23NoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8) \/
        Nonempty
          (M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
            payForCut topologyArc lemma8) \/
          Nonempty
            (M8CommonNeighborNoEarlySourceFamilyData.{u}
              payForCut topologyArc lemma8) \/
            Nonempty
              (M8LocalExclusionNoEarlySourceFamilyData.{u}
                payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        cases D with
        | k23 K =>
            exact Or.inl (Nonempty.intro K)
        | threeCommonNeighbor K =>
            exact Or.inr (Or.inl (Nonempty.intro K))
        | commonNeighbor K =>
            exact Or.inr (Or.inr (Or.inl (Nonempty.intro K)))
        | localExclusion K =>
            exact Or.inr (Or.inr (Or.inr (Nonempty.intro K)))
  case mpr =>
    intro h
    cases h with
    | inl hK23 =>
        cases hK23 with
        | intro K =>
            exact Nonempty.intro (routeDataOfK23Data K)
    | inr hRest =>
        cases hRest with
        | inl hThree =>
            cases hThree with
            | intro K =>
                exact Nonempty.intro (routeDataOfThreeCommonNeighborData K)
        | inr hRest2 =>
            cases hRest2 with
            | inl hCommon =>
                cases hCommon with
                | intro K =>
                    exact Nonempty.intro (routeDataOfCommonNeighborData K)
            | inr hLocal =>
                cases hLocal with
                | intro K =>
                    exact Nonempty.intro (routeDataOfLocalExclusionData K)

theorem not_k23Data_of_not_concreteNoEarlySourceFamily
    (hbad :
      Not
        (Nonempty
          (M8ConcreteNoEarlySourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8K23NoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8)) := by
  intro h
  exact hbad (nonempty_concreteNoEarlySourceFamily_of_k23Data h)

theorem not_threeCommonNeighborData_of_not_concreteNoEarlySourceFamily
    (hbad :
      Not
        (Nonempty
          (M8ConcreteNoEarlySourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8)) := by
  intro h
  exact hbad
    (nonempty_concreteNoEarlySourceFamily_of_threeCommonNeighborData h)

theorem not_commonNeighborData_of_not_concreteNoEarlySourceFamily
    (hbad :
      Not
        (Nonempty
          (M8ConcreteNoEarlySourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8CommonNeighborNoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8)) := by
  intro h
  exact hbad (nonempty_concreteNoEarlySourceFamily_of_commonNeighborData h)

theorem not_localExclusionData_of_not_concreteNoEarlySourceFamily
    (hbad :
      Not
        (Nonempty
          (M8ConcreteNoEarlySourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8LocalExclusionNoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8)) := by
  intro h
  exact hbad (nonempty_concreteNoEarlySourceFamily_of_localExclusionData h)

theorem not_routeData_of_not_concreteNoEarlySourceFamily
    (hbad :
      Not
        (Nonempty
          (M8ConcreteNoEarlySourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8ConcreteNoEarlySourceRouteData.{u}
          payForCut topologyArc lemma8)) := by
  intro h
  exact hbad (nonempty_concreteNoEarlySourceFamily_of_routeData h)

theorem not_routeData_iff_not_each_routeData :
    Not
      (Nonempty
        (M8ConcreteNoEarlySourceRouteData.{u}
          payForCut topologyArc lemma8)) <->
      Not
        (Nonempty
          (M8K23NoEarlySourceFamilyData.{u}
            payForCut topologyArc lemma8)) /\
        Not
          (Nonempty
            (M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
              payForCut topologyArc lemma8)) /\
          Not
            (Nonempty
              (M8CommonNeighborNoEarlySourceFamilyData.{u}
                payForCut topologyArc lemma8)) /\
            Not
              (Nonempty
                (M8LocalExclusionNoEarlySourceFamilyData.{u}
                  payForCut topologyArc lemma8)) := by
  constructor
  · intro hbad
    constructor
    · intro h
      exact hbad ((nonempty_routeData_iff
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).2 (Or.inl h))
    · constructor
      · intro h
        exact hbad ((nonempty_routeData_iff
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)).2 (Or.inr (Or.inl h)))
      · constructor
        · intro h
          exact hbad ((nonempty_routeData_iff
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8)).2 (Or.inr (Or.inr (Or.inl h))))
        · intro h
          exact hbad ((nonempty_routeData_iff
            (payForCut := payForCut) (topologyArc := topologyArc)
            (lemma8 := lemma8)).2 (Or.inr (Or.inr (Or.inr h))))
  · intro hbad hroute
    have hsplit :=
      (nonempty_routeData_iff
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).1 hroute
    cases hsplit with
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

theorem not_each_routeData_of_not_concreteNoEarlySourceFamily
    (hbad :
      Not
        (Nonempty
          (M8ConcreteNoEarlySourceFamily.{u}
            payForCut topologyArc lemma8))) :
      Not
        (Nonempty
          (M8K23NoEarlySourceFamilyData.{u}
            payForCut topologyArc lemma8)) /\
        Not
          (Nonempty
            (M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
              payForCut topologyArc lemma8)) /\
          Not
            (Nonempty
              (M8CommonNeighborNoEarlySourceFamilyData.{u}
                payForCut topologyArc lemma8)) /\
            Not
              (Nonempty
                (M8LocalExclusionNoEarlySourceFamilyData.{u}
                  payForCut topologyArc lemma8)) :=
  (not_routeData_iff_not_each_routeData
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)).1
    (not_routeData_of_not_concreteNoEarlySourceFamily hbad)

end NoEarlyConcreteSourceFamilyW29
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW29ConcreteNoEarlySourceRouteData
    (payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) :=
  Swanepoel.NoEarlyConcreteSourceFamilyW29.M8ConcreteNoEarlySourceRouteData.{u}
    payForCut topologyArc lemma8

theorem swanepoelW29_concreteNoEarlySourceFamily_of_routeData
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (h :
      Nonempty
        (SwanepoelW29ConcreteNoEarlySourceRouteData
          payForCut topologyArc lemma8)) :
    Nonempty
      (Swanepoel.Lemma9NoEarlyObstructionInhabitationW25.M8ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Swanepoel.NoEarlyConcreteSourceFamilyW29.nonempty_concreteNoEarlySourceFamily_of_routeData
    h

theorem swanepoelW29_noRouteData_of_not_concreteNoEarlySourceFamily
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
          (Swanepoel.Lemma9NoEarlyObstructionInhabitationW25.M8ConcreteNoEarlySourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (SwanepoelW29ConcreteNoEarlySourceRouteData
          payForCut topologyArc lemma8)) :=
  Swanepoel.NoEarlyConcreteSourceFamilyW29.not_routeData_of_not_concreteNoEarlySourceFamily
    hbad

end Verified
end ErdosProblems1066

end
