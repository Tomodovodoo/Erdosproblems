import ErdosProblems1066.Swanepoel.Lemma9SourceFamilyConcreteW27

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W28 Lemma 9 no-early source rows

This file is the W28 Lemma 9 worker surface.  It keeps the route honest:
actual source rows are produced only from explicit coverage data together
with K23, three-common-neighbor, common-neighbor-card, or already packaged
local-exclusion obstruction data.

The exact blocker left here is unchanged from W26/W25: after all four
routes are exposed, inhabiting the W20 Lemma 9 source family is equivalent to
inhabiting the W25 coverage-plus-obstruction row family.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9NoEarlySourceRowsW28

open LateTriplesInterface
open Lemma10Bridge
open Lemma6Lemma7AssemblyW13
open Lemma9NoEarlyConstructionW26
open Lemma9NoEarlyInhabitationW24
open Lemma9NoEarlyObstructionInhabitationW25
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

/-! ## Row-level actual source constructors -/

/-- Coverage plus K23 obstruction data gives the actual W20 source row. -/
def sourceFieldsOfCoverageRowAndK23
    (R : M8Lemma9NoEarlyCoverageRow
      payForCut topologyArc lemma8 C hmin)
    (H :
      M8ConcreteK23ObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  (R.toW26K23SourceRow H).toSourceFields

/-- Coverage plus three-common-neighbor obstruction data gives the actual
W20 source row by lowering to K23. -/
def sourceFieldsOfCoverageRowAndThreeCommonNeighbor
    (R : M8Lemma9NoEarlyCoverageRow
      payForCut topologyArc lemma8 C hmin)
    (H :
      K23ObstructionConcrete.M8ConcreteThreeCommonNeighborObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  (R.toW26ThreeCommonNeighborSourceRow H).toSourceFields

/-- Coverage plus common-neighbor-card obstruction data gives the actual W20
source row through the checked W25 common-neighbor obstruction package. -/
def sourceFieldsOfCoverageRowAndCommonNeighbor
    (R : M8Lemma9NoEarlyCoverageRow
      payForCut topologyArc lemma8 C hmin)
    (H :
      K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  (R.toW26CommonNeighborSourceRow H).toSourceFields

/-- Coverage plus an already packaged local-exclusion/no-early obstruction
gives the actual W20 source row directly through W25. -/
def sourceFieldsOfCoverageRowAndLocalExclusionPackage
    (R : M8Lemma9NoEarlyCoverageRow
      payForCut topologyArc lemma8 C hmin)
    (H :
      M8ConcreteNoEarlyObstructionPackage
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  (R.toW25SourceRowOfObstructionPackage H).toSourceFields

/-- The K23 row constructor really is the W26 constructor followed by the
W26-to-W20 forgetful map. -/
@[simp]
theorem sourceFieldsOfCoverageRowAndK23_eq
    (R : M8Lemma9NoEarlyCoverageRow
      payForCut topologyArc lemma8 C hmin)
    (H :
      M8ConcreteK23ObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    sourceFieldsOfCoverageRowAndK23 R H =
      (R.toW26K23SourceRow H).toSourceFields :=
  rfl

/-- The local-exclusion package row constructor is exactly the W25 row
constructor followed by its source-field projection. -/
@[simp]
theorem sourceFieldsOfCoverageRowAndLocalExclusionPackage_eq
    (R : M8Lemma9NoEarlyCoverageRow
      payForCut topologyArc lemma8 C hmin)
    (H :
      M8ConcreteNoEarlyObstructionPackage
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    sourceFieldsOfCoverageRowAndLocalExclusionPackage R H =
      (R.toW25SourceRowOfObstructionPackage H).toSourceFields :=
  rfl

/-! ## Family-level route packages -/

/-- A single W28 sum type for the four checked Lemma 9 no-early source
routes.  Each constructor contains the concrete coverage rows and the
corresponding obstruction rows. -/
inductive M8NoEarlyRouteFamilyData
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  | k23 :
      M8K23NoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8 ->
      M8NoEarlyRouteFamilyData payForCut topologyArc lemma8
  | threeCommonNeighbor :
      M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8 ->
      M8NoEarlyRouteFamilyData payForCut topologyArc lemma8
  | commonNeighbor :
      M8CommonNeighborNoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8 ->
      M8NoEarlyRouteFamilyData payForCut topologyArc lemma8
  | localExclusion :
      M8LocalExclusionNoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8 ->
      M8NoEarlyRouteFamilyData payForCut topologyArc lemma8

namespace M8NoEarlyRouteFamilyData

/-- Forget a checked W28 route package to the W25 no-early source family. -/
def toW25SourceFamily
    (D : M8NoEarlyRouteFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 :=
  match D with
  | M8NoEarlyRouteFamilyData.k23 K =>
      K.toW26SourceFamily.toW25SourceFamily
  | M8NoEarlyRouteFamilyData.threeCommonNeighbor K =>
      K.toW26SourceFamily.toW25SourceFamily
  | M8NoEarlyRouteFamilyData.commonNeighbor K =>
      K.toW26SourceFamily.toW25SourceFamily
  | M8NoEarlyRouteFamilyData.localExclusion K =>
      K.toW25SourceFamily

/-- Forget a checked W28 route package to the W20 Lemma 9 source family. -/
def toSourceFamily
    (D : M8NoEarlyRouteFamilyData.{u}
      payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  D.toW25SourceFamily.toSourceFamily

/-- Forget a checked W28 route package to the W18 producer-family field. -/
def toLemma9CoverageConcreteProducerFamily
    (D : M8NoEarlyRouteFamilyData.{u}
      payForCut topologyArc lemma8) :
    W18Lemma9CoverageConcreteProducerFamily.{u}
      payForCut topologyArc lemma8 :=
  D.toSourceFamily.toLemma9CoverageConcreteProducerFamily

theorem nonempty_w25SourceFamily
    (D : M8NoEarlyRouteFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (M8ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toW25SourceFamily

theorem nonempty_sourceFamily
    (D : M8NoEarlyRouteFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toSourceFamily

theorem nonempty_lemma9CoverageConcreteProducerFamily
    (D : M8NoEarlyRouteFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (W18Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toLemma9CoverageConcreteProducerFamily

end M8NoEarlyRouteFamilyData

/-! ## Positive inhabitants from concrete route data -/

def routeFamilyDataOfK23
    (D : M8K23NoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8NoEarlyRouteFamilyData.{u}
      payForCut topologyArc lemma8 :=
  M8NoEarlyRouteFamilyData.k23 D

def routeFamilyDataOfThreeCommonNeighbor
    (D : M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8NoEarlyRouteFamilyData.{u}
      payForCut topologyArc lemma8 :=
  M8NoEarlyRouteFamilyData.threeCommonNeighbor D

def routeFamilyDataOfCommonNeighbor
    (D : M8CommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8NoEarlyRouteFamilyData.{u}
      payForCut topologyArc lemma8 :=
  M8NoEarlyRouteFamilyData.commonNeighbor D

def routeFamilyDataOfLocalExclusion
    (D : M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8NoEarlyRouteFamilyData.{u}
      payForCut topologyArc lemma8 :=
  M8NoEarlyRouteFamilyData.localExclusion D

theorem nonempty_sourceFamily_of_k23Data
    (D : M8K23NoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  (routeFamilyDataOfK23 D).nonempty_sourceFamily

theorem nonempty_sourceFamily_of_threeCommonNeighborData
    (D : M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  (routeFamilyDataOfThreeCommonNeighbor D).nonempty_sourceFamily

theorem nonempty_sourceFamily_of_commonNeighborData
    (D : M8CommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  (routeFamilyDataOfCommonNeighbor D).nonempty_sourceFamily

theorem nonempty_sourceFamily_of_localExclusionData
    (D : M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  (routeFamilyDataOfLocalExclusion D).nonempty_sourceFamily

/-! ## Exact route-data blockers -/

theorem nonempty_k23Data_iff_coverage_and_k23Obstruction :
    Nonempty
      (M8K23NoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8) <->
      Nonempty
        (M8Lemma9NoEarlyCoverageFamily.{u}
          payForCut topologyArc lemma8) /\
        Nonempty
          (M8K23ObstructionRowFamily.{u}
            payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact And.intro
          (Nonempty.intro D.coverage) (Nonempty.intro D.obstruction)
  case mpr =>
    intro h
    cases h.1 with
    | intro coverage =>
        cases h.2 with
        | intro obstruction =>
            exact Nonempty.intro
              { coverage := coverage
                obstruction := obstruction }

theorem nonempty_threeCommonNeighborData_iff_coverage_and_obstruction :
    Nonempty
      (M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8) <->
      Nonempty
        (M8Lemma9NoEarlyCoverageFamily.{u}
          payForCut topologyArc lemma8) /\
        Nonempty
          (M8ThreeCommonNeighborObstructionRowFamily.{u}
            payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact And.intro
          (Nonempty.intro D.coverage) (Nonempty.intro D.obstruction)
  case mpr =>
    intro h
    cases h.1 with
    | intro coverage =>
        cases h.2 with
        | intro obstruction =>
            exact Nonempty.intro
              { coverage := coverage
                obstruction := obstruction }

theorem nonempty_commonNeighborData_iff_coverage_and_obstruction :
    Nonempty
      (M8CommonNeighborNoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8) <->
      Nonempty
        (M8Lemma9NoEarlyCoverageFamily.{u}
          payForCut topologyArc lemma8) /\
        Nonempty
          (M8CommonNeighborCardObstructionRowFamily.{u}
            payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact And.intro
          (Nonempty.intro D.coverage) (Nonempty.intro D.obstruction)
  case mpr =>
    intro h
    cases h.1 with
    | intro coverage =>
        cases h.2 with
        | intro obstruction =>
            exact Nonempty.intro
              { coverage := coverage
                obstruction := obstruction }

theorem nonempty_localExclusionData_iff_coverage_and_obstruction :
    Nonempty
      (M8LocalExclusionNoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8) <->
      Nonempty
        (M8Lemma9NoEarlyCoverageFamily.{u}
          payForCut topologyArc lemma8) /\
        Nonempty
          (M8LocalExclusionObstructionPackageFamily.{u}
            payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact And.intro
          (Nonempty.intro D.coverage) (Nonempty.intro D.obstruction)
  case mpr =>
    intro h
    cases h.1 with
    | intro coverage =>
        cases h.2 with
        | intro obstruction =>
            exact Nonempty.intro
              { coverage := coverage
                obstruction := obstruction }

/-- Any checked W28 route is sufficient for the exact W25 blocker. -/
theorem nonempty_w25SourceFamily_of_routeData
    (h :
      Nonempty
        (M8NoEarlyRouteFamilyData.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (M8ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) := by
  cases h with
  | intro D =>
      exact D.nonempty_w25SourceFamily

/-- Exact remaining Lemma 9 blocker after the W28 route split. -/
theorem nonempty_sourceFamily_iff_w25NoEarlySourceFamily :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) <->
      Nonempty
        (M8ConcreteNoEarlySourceFamily.{u}
          payForCut topologyArc lemma8) :=
  Lemma9NoEarlyConstructionW26.nonempty_sourceFamily_iff_w25NoEarlySourceFamily
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem nonempty_sourceFamily_of_routeData
    (h :
      Nonempty
        (M8NoEarlyRouteFamilyData.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  (nonempty_sourceFamily_iff_w25NoEarlySourceFamily
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)).mpr
    (nonempty_w25SourceFamily_of_routeData h)

theorem not_routeData_of_not_sourceFamily
    (hbad :
      Not
        (Nonempty
          (Lemma9NatLateTripleSourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8NoEarlyRouteFamilyData.{u}
          payForCut topologyArc lemma8)) := by
  intro hroute
  exact hbad (nonempty_sourceFamily_of_routeData hroute)

theorem not_k23Data_of_not_sourceFamily
    (hbad :
      Not
        (Nonempty
          (Lemma9NatLateTripleSourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8K23NoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8)) := by
  intro h
  cases h with
  | intro D =>
      exact hbad (nonempty_sourceFamily_of_k23Data D)

theorem not_threeCommonNeighborData_of_not_sourceFamily
    (hbad :
      Not
        (Nonempty
          (Lemma9NatLateTripleSourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8)) := by
  intro h
  cases h with
  | intro D =>
      exact hbad (nonempty_sourceFamily_of_threeCommonNeighborData D)

theorem not_commonNeighborData_of_not_sourceFamily
    (hbad :
      Not
        (Nonempty
          (Lemma9NatLateTripleSourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8CommonNeighborNoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8)) := by
  intro h
  cases h with
  | intro D =>
      exact hbad (nonempty_sourceFamily_of_commonNeighborData D)

theorem not_localExclusionData_of_not_sourceFamily
    (hbad :
      Not
        (Nonempty
          (Lemma9NatLateTripleSourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8LocalExclusionNoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8)) := by
  intro h
  cases h with
  | intro D =>
      exact hbad (nonempty_sourceFamily_of_localExclusionData D)

end Lemma9NoEarlySourceRowsW28
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW28Lemma9NoEarlyRouteFamilyData
    (payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) :=
  Swanepoel.Lemma9NoEarlySourceRowsW28.M8NoEarlyRouteFamilyData.{u}
    payForCut topologyArc lemma8

theorem swanepoelW28_lemma9_sourceFamily_iff_w25NoEarlySourceFamily
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    Nonempty
      (Swanepoel.Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) <->
      Nonempty
        (Swanepoel.Lemma9NoEarlyObstructionInhabitationW25.M8ConcreteNoEarlySourceFamily.{u}
          payForCut topologyArc lemma8) :=
  Swanepoel.Lemma9NoEarlySourceRowsW28.nonempty_sourceFamily_iff_w25NoEarlySourceFamily
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem swanepoelW28_lemma9_sourceFamily_of_routeData
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (h :
      Nonempty
        (SwanepoelW28Lemma9NoEarlyRouteFamilyData
          payForCut topologyArc lemma8)) :
    Nonempty
      (Swanepoel.Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Swanepoel.Lemma9NoEarlySourceRowsW28.nonempty_sourceFamily_of_routeData h

end Verified
end ErdosProblems1066

end
