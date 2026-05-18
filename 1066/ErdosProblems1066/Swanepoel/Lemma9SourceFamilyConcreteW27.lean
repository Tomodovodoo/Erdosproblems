import ErdosProblems1066.Swanepoel.Lemma9NoEarlyConstructionW26

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W27 concrete Lemma 9 source-family constructors

This file is the SW6 Lemma 9 source-family worker.  It builds actual W26
source-family inhabitants from explicit coverage rows together with one of the
checked no-early obstruction routes:

* labelled `K_{2,3}` obstruction data;
* three-common-neighbor obstruction data, lowered to `K_{2,3}`;
* common-neighbor-card obstruction data;
* an already packaged local-exclusion/no-early obstruction row.

The constructions below are forward constructors.  They do not use the W25
inhabitation equivalence as a substitute for source data.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9SourceFamilyConcreteW27

open LateTriplesInterface
open Lemma10Bridge
open Lemma6Lemma7AssemblyW13
open Lemma9NoEarlyConstructionW26
open Lemma9NoEarlyInhabitationW24
open Lemma9NoEarlyObstructionInhabitationW25
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

/-! ## Shared coverage rows -/

/-- The coverage half of a W26 Lemma 9 no-early source row. -/
structure M8Lemma9NoEarlyCoverageRow
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

namespace M8Lemma9NoEarlyCoverageRow

/-- Add K23 obstruction data to a coverage row, producing the actual W26 K23
source row. -/
def toW26K23SourceRow
    (R : M8Lemma9NoEarlyCoverageRow
      payForCut topologyArc lemma8 C hmin)
    (H :
      M8ConcreteK23ObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    M8K23NoEarlySourceRow
      payForCut topologyArc lemma8 C hmin where
  longArcCount := R.longArcCount
  coverage := R.coverage
  k23Obstruction := H

/-- Add three-common-neighbor obstruction data to a coverage row, producing
the actual W26 three-common-neighbor source row. -/
def toW26ThreeCommonNeighborSourceRow
    (R : M8Lemma9NoEarlyCoverageRow
      payForCut topologyArc lemma8 C hmin)
    (H :
      K23ObstructionConcrete.M8ConcreteThreeCommonNeighborObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    M8ThreeCommonNeighborNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin where
  longArcCount := R.longArcCount
  coverage := R.coverage
  threeCommonNeighbor := H

/-- Add common-neighbor-card obstruction data to a coverage row, producing
the actual W26 common-neighbor-card source row. -/
def toW26CommonNeighborSourceRow
    (R : M8Lemma9NoEarlyCoverageRow
      payForCut topologyArc lemma8 C hmin)
    (H :
      K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    M8CommonNeighborNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin where
  longArcCount := R.longArcCount
  coverage := R.coverage
  commonNeighborObstruction := H

/-- Add an already packaged no-early/local-exclusion obstruction row to a
coverage row, producing the W25 concrete source row directly. -/
def toW25SourceRowOfObstructionPackage
    (R : M8Lemma9NoEarlyCoverageRow
      payForCut topologyArc lemma8 C hmin)
    (H :
      M8ConcreteNoEarlyObstructionPackage
        (RowPredicates payForCut topologyArc lemma8 C hmin)) :
    M8ConcreteNoEarlySourceRow
      payForCut topologyArc lemma8 C hmin where
  longArcCount := R.longArcCount
  coverage := R.coverage
  obstruction := H

end M8Lemma9NoEarlyCoverageRow

/-- Uniform coverage rows for the W26 Lemma 9 no-early source constructors. -/
structure M8Lemma9NoEarlyCoverageFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8Lemma9NoEarlyCoverageRow
          payForCut topologyArc lemma8 C hmin

/-! ## Obstruction row families -/

/-- Uniform K23 obstruction rows matching the assembled W26 row predicates. -/
structure M8K23ObstructionRowFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8ConcreteK23ObstructionInputs
          (RowPredicates payForCut topologyArc lemma8 C hmin)

/-- Uniform three-common-neighbor obstruction rows matching the assembled W26
row predicates. -/
structure M8ThreeCommonNeighborObstructionRowFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23ObstructionConcrete.M8ConcreteThreeCommonNeighborObstructionInputs
          (RowPredicates payForCut topologyArc lemma8 C hmin)

/-- Uniform common-neighbor-card obstruction rows matching the assembled W26
row predicates. -/
structure M8CommonNeighborCardObstructionRowFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
          (RowPredicates payForCut topologyArc lemma8 C hmin)

/-- Uniform already packaged local-exclusion/no-early obstruction rows. -/
structure M8LocalExclusionObstructionPackageFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8ConcreteNoEarlyObstructionPackage
          (RowPredicates payForCut topologyArc lemma8 C hmin)

/-! ## W26 family inhabitants from concrete K23/common-neighbor data -/

/-- Concrete inputs for the W26 K23 source family. -/
structure M8K23NoEarlySourceFamilyData
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  coverage :
    M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8
  obstruction :
    M8K23ObstructionRowFamily.{u} payForCut topologyArc lemma8

namespace M8K23NoEarlySourceFamilyData

/-- Build the actual W26 K23 no-early source family. -/
def toW26SourceFamily
    (D : M8K23NoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8K23NoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (D.coverage.row C hmin).toW26K23SourceRow
      (D.obstruction.row C hmin)

/-- Forget the concrete K23 route to the W20 Lemma 9 source family. -/
def toSourceFamily
    (D : M8K23NoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  D.toW26SourceFamily.toSourceFamily

theorem nonempty_w26SourceFamily
    (D : M8K23NoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (M8K23NoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toW26SourceFamily

theorem nonempty_sourceFamily
    (D : M8K23NoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toSourceFamily

end M8K23NoEarlySourceFamilyData

/-- Concrete inputs for the W26 three-common-neighbor source family. -/
structure M8ThreeCommonNeighborNoEarlySourceFamilyData
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  coverage :
    M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8
  obstruction :
    M8ThreeCommonNeighborObstructionRowFamily.{u}
      payForCut topologyArc lemma8

namespace M8ThreeCommonNeighborNoEarlySourceFamilyData

/-- Build the actual W26 three-common-neighbor no-early source family. -/
def toW26SourceFamily
    (D : M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8ThreeCommonNeighborNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (D.coverage.row C hmin).toW26ThreeCommonNeighborSourceRow
      (D.obstruction.row C hmin)

/-- Lower the W26 three-common-neighbor source family to the W26 K23 source
family. -/
def toW26K23SourceFamily
    (D : M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8K23NoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 :=
  D.toW26SourceFamily.toK23SourceFamily

/-- Forget the concrete three-common-neighbor route to the W20 Lemma 9 source
family. -/
def toSourceFamily
    (D : M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  D.toW26SourceFamily.toSourceFamily

theorem nonempty_w26SourceFamily
    (D : M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (M8ThreeCommonNeighborNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toW26SourceFamily

theorem nonempty_w26K23SourceFamily
    (D : M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (M8K23NoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toW26K23SourceFamily

theorem nonempty_sourceFamily
    (D : M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toSourceFamily

end M8ThreeCommonNeighborNoEarlySourceFamilyData

/-- Concrete inputs for the W26 common-neighbor-card source family. -/
structure M8CommonNeighborNoEarlySourceFamilyData
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  coverage :
    M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8
  obstruction :
    M8CommonNeighborCardObstructionRowFamily.{u}
      payForCut topologyArc lemma8

namespace M8CommonNeighborNoEarlySourceFamilyData

/-- Build the actual W26 common-neighbor-card no-early source family. -/
def toW26SourceFamily
    (D : M8CommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8CommonNeighborNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (D.coverage.row C hmin).toW26CommonNeighborSourceRow
      (D.obstruction.row C hmin)

/-- Lower the W26 common-neighbor-card source family to the W26 K23 source
family. -/
def toW26K23SourceFamily
    (D : M8CommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8K23NoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 :=
  D.toW26SourceFamily.toK23SourceFamily

/-- Forget the concrete common-neighbor-card route to the W20 Lemma 9 source
family. -/
def toSourceFamily
    (D : M8CommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  D.toW26SourceFamily.toSourceFamily

theorem nonempty_w26SourceFamily
    (D : M8CommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (M8CommonNeighborNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toW26SourceFamily

theorem nonempty_w26K23SourceFamily
    (D : M8CommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (M8K23NoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toW26K23SourceFamily

theorem nonempty_sourceFamily
    (D : M8CommonNeighborNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toSourceFamily

end M8CommonNeighborNoEarlySourceFamilyData

/-! ## Explicit local-exclusion package route -/

/-- Concrete inputs carrying the already packaged local-exclusion/no-early
row.  This still constructs source rows directly rather than appealing to an
inhabitation equivalence. -/
structure M8LocalExclusionNoEarlySourceFamilyData
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  coverage :
    M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8
  obstruction :
    M8LocalExclusionObstructionPackageFamily.{u}
      payForCut topologyArc lemma8

namespace M8LocalExclusionNoEarlySourceFamilyData

/-- Build the W25 concrete source family from explicit local-exclusion
obstruction packages. -/
def toW25SourceFamily
    (D : M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    M8ConcreteNoEarlySourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (D.coverage.row C hmin).toW25SourceRowOfObstructionPackage
      (D.obstruction.row C hmin)

/-- Forget the local-exclusion package route to the W20 Lemma 9 source
family. -/
def toSourceFamily
    (D : M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Lemma9NatLateTripleSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  D.toW25SourceFamily.toSourceFamily

theorem nonempty_w25SourceFamily
    (D : M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (M8ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toW25SourceFamily

theorem nonempty_sourceFamily
    (D : M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8) :
    Nonempty
      (Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro D.toSourceFamily

end M8LocalExclusionNoEarlySourceFamilyData

/-! ## Explicit finite-local-exclusion K23/common-neighbor package builders -/

/-- Rowwise finite local-exclusion packages matching the unit-distance row
graph. -/
structure M8FiniteLocalExclusionFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (_hmin : IsMinimalClearedFailure C),
        FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C)

namespace M8FiniteLocalExclusionFamily

/-- The finite local-exclusion family supplied by minimality. -/
def ofMinimalFailures : M8FiniteLocalExclusionFamily.{u} where
  row := fun _C hmin =>
    K23ObstructionConcrete.finiteLocalExclusionPackage_of_minimalFailure_noAssumptions
      hmin

end M8FiniteLocalExclusionFamily

/-- Package K23 obstruction rows with explicit finite local exclusions as
local-exclusion obstruction packages. -/
def localExclusionPackageFamilyOfK23
    (K : M8K23ObstructionRowFamily.{u}
      payForCut topologyArc lemma8)
    (E : M8FiniteLocalExclusionFamily.{u}) :
    M8LocalExclusionObstructionPackageFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    M8ConcreteNoEarlyObstructionPackage.k23
      (K.row C hmin) (E.row C hmin)

/-- Package three-common-neighbor obstruction rows with explicit finite local
exclusions as local-exclusion obstruction packages. -/
def localExclusionPackageFamilyOfThreeCommonNeighbor
    (K : M8ThreeCommonNeighborObstructionRowFamily.{u}
      payForCut topologyArc lemma8)
    (E : M8FiniteLocalExclusionFamily.{u}) :
    M8LocalExclusionObstructionPackageFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    M8ConcreteNoEarlyObstructionPackage.k23
      ((K.row C hmin).toK23ObstructionInputs) (E.row C hmin)

/-- Package common-neighbor-card obstruction rows with explicit finite local
exclusions as local-exclusion obstruction packages. -/
def localExclusionPackageFamilyOfCommonNeighbor
    (K : M8CommonNeighborCardObstructionRowFamily.{u}
      payForCut topologyArc lemma8)
    (E : M8FiniteLocalExclusionFamily.{u}) :
    M8LocalExclusionObstructionPackageFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    M8ConcreteNoEarlyObstructionPackage.commonNeighbor
      (K.row C hmin) (E.row C hmin)

/-- K23 data plus explicit finite local exclusions give the local-exclusion
source-family route. -/
def localExclusionSourceFamilyDataOfK23
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (K : M8K23ObstructionRowFamily.{u}
      payForCut topologyArc lemma8)
    (E : M8FiniteLocalExclusionFamily.{u}) :
    M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8 where
  coverage := coverage
  obstruction := localExclusionPackageFamilyOfK23 K E

/-- Three-common-neighbor data plus explicit finite local exclusions give the
local-exclusion source-family route. -/
def localExclusionSourceFamilyDataOfThreeCommonNeighbor
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (K : M8ThreeCommonNeighborObstructionRowFamily.{u}
      payForCut topologyArc lemma8)
    (E : M8FiniteLocalExclusionFamily.{u}) :
    M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8 where
  coverage := coverage
  obstruction := localExclusionPackageFamilyOfThreeCommonNeighbor K E

/-- Common-neighbor-card data plus explicit finite local exclusions give the
local-exclusion source-family route. -/
def localExclusionSourceFamilyDataOfCommonNeighbor
    (coverage :
      M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)
    (K : M8CommonNeighborCardObstructionRowFamily.{u}
      payForCut topologyArc lemma8)
    (E : M8FiniteLocalExclusionFamily.{u}) :
    M8LocalExclusionNoEarlySourceFamilyData.{u}
      payForCut topologyArc lemma8 where
  coverage := coverage
  obstruction := localExclusionPackageFamilyOfCommonNeighbor K E

end Lemma9SourceFamilyConcreteW27
end Swanepoel
end ErdosProblems1066

end
