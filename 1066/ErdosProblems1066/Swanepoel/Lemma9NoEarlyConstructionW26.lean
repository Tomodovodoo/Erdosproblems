import ErdosProblems1066.Swanepoel.K23CommonNeighborW11
import ErdosProblems1066.Swanepoel.Lemma9NoEarlyObstructionInhabitationW25

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W26 Lemma 9 no-early construction boundary

This file is the Swanepoel W26 SW5 worker pass.  It does not assert a new
unconditional Lemma 9 source row.  Instead it constructs the checked W25
source rows from the available local routes:

* checked coverage plus K23 obstruction data;
* checked coverage plus three-common-neighbor data;
* checked coverage plus common-neighbor-card data;
* the finite local-exclusion package supplied by minimality.

The final section records the exact blocker left by this pass: the W20 Lemma 9
source family is inhabited exactly when the existing W25
`M8ConcreteNoEarlySourceFamily` is inhabited.  Thus an attempted K23 or
common-neighbor construction has a precise remaining row family rather than a
hidden assumption.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9NoEarlyConstructionW26

open LateTriplesInterface
open Lemma10Bridge
open Lemma6Lemma7AssemblyW13
open Lemma9NoEarlyObstructionInhabitationW25
open Lemma9NoEarlyInhabitationW24
open Lemma9ProducerFamilyW20
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

/-! ## Pointwise K23/common-neighbor source rows -/

/-- A pointwise K23 route for the W20 Lemma 9 row: checked coverage for the
assembled row together with K23 obstruction data for the same predicates. -/
structure M8K23NoEarlySourceRow
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) where
  longArcCount : Nat
  coverage :
    GapNegativeCoverageData
      (RowBoundary payForCut topologyArc lemma8 C hmin)
      longArcCount
  k23Obstruction :
    M8ConcreteK23ObstructionInputs
      (RowPredicates payForCut topologyArc lemma8 C hmin)

namespace M8K23NoEarlySourceRow

/-- Minimality supplies the finite local-exclusion package used to close the
K23 obstruction into the W25 no-early obstruction package. -/
def finiteLocalExclusions
    (_R : M8K23NoEarlySourceRow
      payForCut topologyArc lemma8 C hmin) :
    FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C) :=
  K23ObstructionConcrete.finiteLocalExclusionPackage_of_minimalFailure_noAssumptions
    hmin

/-- Feed a K23 row into the existing W25 source-row package. -/
def toW25SourceRow
    (R : M8K23NoEarlySourceRow
      payForCut topologyArc lemma8 C hmin) :
    M8ConcreteNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin where
  longArcCount := R.longArcCount
  coverage := R.coverage
  obstruction :=
    M8ConcreteNoEarlyObstructionPackage.k23
      R.k23Obstruction R.finiteLocalExclusions

/-- Feed a K23 row all the way to the W20 Lemma 9 source fields. -/
def toSourceFields
    (R : M8K23NoEarlySourceRow
      payForCut topologyArc lemma8 C hmin) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  R.toW25SourceRow.toSourceFields

end M8K23NoEarlySourceRow

/-- A pointwise three-common-neighbor route.  It is stronger than the K23
route, and is lowered to K23 by the existing checked adapter. -/
structure M8ThreeCommonNeighborNoEarlySourceRow
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) where
  longArcCount : Nat
  coverage :
    GapNegativeCoverageData
      (RowBoundary payForCut topologyArc lemma8 C hmin)
      longArcCount
  threeCommonNeighbor :
    K23ObstructionConcrete.M8ConcreteThreeCommonNeighborObstructionInputs
      (RowPredicates payForCut topologyArc lemma8 C hmin)

namespace M8ThreeCommonNeighborNoEarlySourceRow

/-- Forget three-common-neighbor witnesses to the K23 pointwise route. -/
def toK23SourceRow
    (R : M8ThreeCommonNeighborNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin) :
    M8K23NoEarlySourceRow
      payForCut topologyArc lemma8 C hmin where
  longArcCount := R.longArcCount
  coverage := R.coverage
  k23Obstruction := R.threeCommonNeighbor.toK23ObstructionInputs

/-- Feed a three-common-neighbor row into the existing W25 source-row
package. -/
def toW25SourceRow
    (R : M8ThreeCommonNeighborNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin) :
    M8ConcreteNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin :=
  R.toK23SourceRow.toW25SourceRow

/-- Feed a three-common-neighbor row to the W20 Lemma 9 source fields. -/
def toSourceFields
    (R : M8ThreeCommonNeighborNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  R.toW25SourceRow.toSourceFields

end M8ThreeCommonNeighborNoEarlySourceRow

/-- A pointwise common-neighbor-card route for the W20 Lemma 9 row. -/
structure M8CommonNeighborNoEarlySourceRow
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) where
  longArcCount : Nat
  coverage :
    GapNegativeCoverageData
      (RowBoundary payForCut topologyArc lemma8 C hmin)
      longArcCount
  commonNeighborObstruction :
    K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
      (RowPredicates payForCut topologyArc lemma8 C hmin)

namespace M8CommonNeighborNoEarlySourceRow

/-- Minimality supplies the common-neighbor-card cap through the same finite
local-exclusion package used by the W25 common-neighbor constructor. -/
def finiteLocalExclusions
    (_R : M8CommonNeighborNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin) :
    FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C) :=
  K23ObstructionConcrete.finiteLocalExclusionPackage_of_minimalFailure_noAssumptions
    hmin

/-- Forget common-neighbor-card witnesses to the K23 pointwise route. -/
def toK23SourceRow
    (R : M8CommonNeighborNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin) :
    M8K23NoEarlySourceRow
      payForCut topologyArc lemma8 C hmin where
  longArcCount := R.longArcCount
  coverage := R.coverage
  k23Obstruction := R.commonNeighborObstruction.toK23ObstructionInputs

/-- Feed a common-neighbor-card row into the existing W25 source-row package
without going through an untracked assumption. -/
def toW25SourceRow
    (R : M8CommonNeighborNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin) :
    M8ConcreteNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin where
  longArcCount := R.longArcCount
  coverage := R.coverage
  obstruction :=
    M8ConcreteNoEarlyObstructionPackage.commonNeighbor
      R.commonNeighborObstruction R.finiteLocalExclusions

/-- Feed a common-neighbor-card row to the W20 Lemma 9 source fields. -/
def toSourceFields
    (R : M8CommonNeighborNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin) :
    SourceFields payForCut topologyArc lemma8 C hmin :=
  R.toW25SourceRow.toSourceFields

end M8CommonNeighborNoEarlySourceRow

/-! ## Family routes into W25 and W20 -/

/-- Uniform K23 source rows for the W20 Lemma 9 row. -/
structure M8K23NoEarlySourceFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8K23NoEarlySourceRow
          payForCut topologyArc lemma8 C hmin

namespace M8K23NoEarlySourceFamily

/-- Uniform K23 rows feed the existing W25 source family. -/
def toW25SourceFamily
    (F : M8K23NoEarlySourceFamily.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin => (F.row C hmin).toW25SourceRow

/-- Uniform K23 rows feed the W20 Lemma 9 source family. -/
def toSourceFamily
    (F : M8K23NoEarlySourceFamily.{u}
      payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  F.toW25SourceFamily.toSourceFamily

end M8K23NoEarlySourceFamily

/-- Uniform three-common-neighbor source rows. -/
structure M8ThreeCommonNeighborNoEarlySourceFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8ThreeCommonNeighborNoEarlySourceRow
          payForCut topologyArc lemma8 C hmin

namespace M8ThreeCommonNeighborNoEarlySourceFamily

/-- Uniform three-common-neighbor rows feed the K23 route. -/
def toK23SourceFamily
    (F : M8ThreeCommonNeighborNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8) :
    M8K23NoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin => (F.row C hmin).toK23SourceRow

/-- Uniform three-common-neighbor rows feed the existing W25 source family. -/
def toW25SourceFamily
    (F : M8ThreeCommonNeighborNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 :=
  F.toK23SourceFamily.toW25SourceFamily

/-- Uniform three-common-neighbor rows feed the W20 Lemma 9 source family. -/
def toSourceFamily
    (F : M8ThreeCommonNeighborNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  F.toW25SourceFamily.toSourceFamily

end M8ThreeCommonNeighborNoEarlySourceFamily

/-- Uniform common-neighbor-card source rows. -/
structure M8CommonNeighborNoEarlySourceFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8CommonNeighborNoEarlySourceRow
          payForCut topologyArc lemma8 C hmin

namespace M8CommonNeighborNoEarlySourceFamily

/-- Uniform common-neighbor rows feed the K23 route. -/
def toK23SourceFamily
    (F : M8CommonNeighborNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8) :
    M8K23NoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin => (F.row C hmin).toK23SourceRow

/-- Uniform common-neighbor rows feed the existing W25 source family. -/
def toW25SourceFamily
    (F : M8CommonNeighborNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin => (F.row C hmin).toW25SourceRow

/-- Uniform common-neighbor rows feed the W20 Lemma 9 source family. -/
def toSourceFamily
    (F : M8CommonNeighborNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  F.toW25SourceFamily.toSourceFamily

end M8CommonNeighborNoEarlySourceFamily

theorem nonempty_sourceFamily_of_k23NoEarlySourceFamily
    (F : M8K23NoEarlySourceFamily.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro F.toSourceFamily

theorem nonempty_sourceFamily_of_threeCommonNeighborNoEarlySourceFamily
    (F : M8ThreeCommonNeighborNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro F.toSourceFamily

theorem nonempty_sourceFamily_of_commonNeighborNoEarlySourceFamily
    (F : M8CommonNeighborNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro F.toSourceFamily

/-! ## Exact blocker surface -/

/-- The existing W25 obstruction-source family has exactly the same
inhabitation content as the W20 Lemma 9 source family.  This is the precise
blocker left if the K23/common-neighbor rows cannot be built. -/
theorem nonempty_sourceFamily_iff_w25NoEarlySourceFamily :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) <->
      Nonempty
        (M8ConcreteNoEarlySourceFamily.{u}
          payForCut topologyArc lemma8) := by
  constructor
  case mp =>
    intro hsource
    have hrows :
        forall {n : Nat} (C : _root_.UDConfig n)
          (hmin : IsMinimalClearedFailure C),
            Nonempty
              (M8ConcreteNoEarlySourceRow
                payForCut topologyArc lemma8 C hmin) :=
      (nonempty_sourceFamily_iff_forall_obstructionSourceRow
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)).mp hsource
    exact
      Nonempty.intro
        { row := fun C hmin => Classical.choice (hrows C hmin) }
  case mpr =>
    intro hfamily
    rcases hfamily with ⟨F⟩
    exact Nonempty.intro F.toSourceFamily

/-- If the W20 Lemma 9 source family is absent, then the existing W25
obstruction-source family is exactly the uninhabited row family. -/
theorem not_w25NoEarlySourceFamily_of_not_sourceFamily
    (hbad :
      Not
        (Nonempty
          (Lemma9NatLateTripleSourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8ConcreteNoEarlySourceFamily.{u}
          payForCut topologyArc lemma8)) := by
  intro hfamily
  exact hbad
    ((nonempty_sourceFamily_iff_w25NoEarlySourceFamily
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8)).mpr hfamily)

/-- Failure of the W20 Lemma 9 source family also rules out the specific K23
construction route exposed in this file. -/
theorem not_k23NoEarlySourceFamily_of_not_sourceFamily
    (hbad :
      Not
        (Nonempty
          (Lemma9NatLateTripleSourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8K23NoEarlySourceFamily.{u}
          payForCut topologyArc lemma8)) := by
  intro hfamily
  rcases hfamily with ⟨F⟩
  exact hbad (nonempty_sourceFamily_of_k23NoEarlySourceFamily F)

/-- Failure of the W20 Lemma 9 source family rules out the stronger
three-common-neighbor construction route. -/
theorem not_threeCommonNeighborNoEarlySourceFamily_of_not_sourceFamily
    (hbad :
      Not
        (Nonempty
          (Lemma9NatLateTripleSourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8ThreeCommonNeighborNoEarlySourceFamily.{u}
          payForCut topologyArc lemma8)) := by
  intro hfamily
  rcases hfamily with ⟨F⟩
  exact hbad
    (nonempty_sourceFamily_of_threeCommonNeighborNoEarlySourceFamily F)

/-- Failure of the W20 Lemma 9 source family rules out the common-neighbor
construction route exposed in this file. -/
theorem not_commonNeighborNoEarlySourceFamily_of_not_sourceFamily
    (hbad :
      Not
        (Nonempty
          (Lemma9NatLateTripleSourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (M8CommonNeighborNoEarlySourceFamily.{u}
          payForCut topologyArc lemma8)) := by
  intro hfamily
  rcases hfamily with ⟨F⟩
  exact hbad (nonempty_sourceFamily_of_commonNeighborNoEarlySourceFamily F)

end Lemma9NoEarlyConstructionW26
end Swanepoel
end ErdosProblems1066

end
