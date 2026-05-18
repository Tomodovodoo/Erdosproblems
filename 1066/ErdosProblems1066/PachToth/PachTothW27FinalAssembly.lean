import ErdosProblems1066.PachToth.ArbitraryNFinalAssemblyW26
import ErdosProblems1066.PachToth.ClosedPlacementConcreteConstructionW26
import ErdosProblems1066.PachToth.ConcreteReducedMetricCertificatesW26
import ErdosProblems1066.PachToth.ExactTargetClosureW26
import ErdosProblems1066.PachToth.PeriodBaseFixingSameW16
import ErdosProblems1066.PachToth.PositiveExactChainPackageW26

set_option autoImplicit false

/-!
# W27 final Pach-Toth assembly

This file is deliberately an internal final assembly layer.  It does not edit
public known-bound wrappers and it does not manufacture an unconditional
Pach-Toth endpoint from target repackaging.

The W26/W27 source packages close the exact and arbitrary targets from actual
concrete source data, with the nearest current concrete source being the
non-connector lower-table family.  That family is still not inhabited: its
smallest concrete dependency is the period-search data, whose transition field
is the strong same/opposite role-hinge package already proved empty.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW27FinalAssembly

noncomputable section

/-! ## Endpoint vocabulary -/

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactAndArbitraryTargets : Prop :=
  ExactTarget /\ ArbitraryTarget

/-! ## Existing W26/W27 source vocabulary -/

abbrev SmallestExactSourcePackage : Type :=
  ExactTargetClosureW26.SmallestExactSourcePackage

abbrev PositiveExactChainPackage : Type :=
  PositiveExactChainPackageW26.PositiveExactChainPackage

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PositiveExactChainPackageW26.RemainingPositiveExactChainBlocker

abbrev ConcretePeriodSearchData : Type :=
  ConcretePeriodSearchFamily.PeriodSearchData

abbrev SmallestConcreteSourceDependency : Type :=
  ConcretePeriodSearchData

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  ConcreteReducedMetricCertificatesW26.ConcreteNonConnectorLowerTableFamily

abbrev ConcreteReducedMetricCertificate : Type :=
  ConcreteReducedMetricCertificatesW26.ConcreteReducedMetricCertificate

abbrev ConcreteClosedOrbitFamily : Type :=
  ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily

/-! ## Exact/arbitrary closure from genuine source packages -/

theorem arbitraryTarget_of_exactTarget
    (H : ExactTarget) :
    ArbitraryTarget :=
  ArbitraryNFinalAssemblyW26.arbitraryTarget_of_exactTarget_translatedRemainder
    H

theorem exactTarget_of_arbitraryTarget
    (H : ArbitraryTarget) :
    ExactTarget :=
  ArbitraryNFinalAssemblyW26.exactTarget_of_arbitraryTarget H

theorem exactTarget_iff_arbitraryTarget :
    ExactTarget <-> ArbitraryTarget :=
  ArbitraryNFinalAssemblyW26.exactTarget_iff_arbitraryTarget

theorem exactAndArbitraryTargets_of_exactTarget
    (H : ExactTarget) :
    ExactAndArbitraryTargets :=
  And.intro H (arbitraryTarget_of_exactTarget H)

theorem exactAndArbitraryTargets_iff_exactTarget :
    ExactAndArbitraryTargets <-> ExactTarget := by
  constructor
  case mp =>
    intro H
    exact H.1
  case mpr =>
    exact exactAndArbitraryTargets_of_exactTarget

theorem exactAndArbitraryTargets_iff_smallestExactSourcePackage :
    ExactAndArbitraryTargets <->
      Nonempty SmallestExactSourcePackage := by
  exact Iff.trans exactAndArbitraryTargets_iff_exactTarget
    ExactTargetClosureW26.exactTarget_iff_nonempty_smallestExactSourcePackage

theorem exactAndArbitraryTargets_of_smallestExactSourcePackage
    (P : SmallestExactSourcePackage) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_iff_smallestExactSourcePackage.mpr
    (Nonempty.intro P)

theorem exactAndArbitraryTargets_of_positiveExactChainPackage
    (P : PositiveExactChainPackage) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_smallestExactSourcePackage P

theorem exactAndArbitraryTargets_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ExactAndArbitraryTargets :=
  And.intro
    (ConcreteReducedMetricCertificatesW26.exactTarget_of_concreteLowerTables C)
    (ConcreteReducedMetricCertificatesW26.arbitraryTarget_of_concreteLowerTables C)

theorem exactAndArbitraryTargets_of_nonempty_concreteLowerTables
    (H : Nonempty ConcreteNonConnectorLowerTableFamily) :
    ExactAndArbitraryTargets := by
  cases H with
  | intro C =>
      exact exactAndArbitraryTargets_of_concreteLowerTables C

theorem exactAndArbitraryTargets_of_concreteReducedMetricCertificate
    (C : ConcreteReducedMetricCertificate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_concreteLowerTables C.lowerTables

theorem exactAndArbitraryTargets_of_concreteClosedOrbitFamily
    (C : ConcreteClosedOrbitFamily) :
    ExactAndArbitraryTargets :=
  And.intro
    (ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily.exactTarget C)
    (ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily.arbitraryTarget C)

/-! ## The precise no-fake concrete blocker -/

theorem nonempty_smallestConcreteSourceDependency_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty SmallestConcreteSourceDependency :=
  Nonempty.intro C.periodSearch

theorem nonempty_smallestConcreteSourceDependency_of_nonempty_concreteLowerTables
    (H : Nonempty ConcreteNonConnectorLowerTableFamily) :
    Nonempty SmallestConcreteSourceDependency := by
  cases H with
  | intro C =>
      exact nonempty_smallestConcreteSourceDependency_of_concreteLowerTables C

theorem not_nonempty_smallestConcreteSourceDependency :
    Not (Nonempty SmallestConcreteSourceDependency) := by
  intro H
  cases H with
  | intro P =>
      exact PeriodBaseFixingSameW16.not_nonempty_roleHingeTransitions
        (Nonempty.intro P.transitions)

theorem not_nonempty_concreteLowerTables :
    Not (Nonempty ConcreteNonConnectorLowerTableFamily) := by
  intro H
  exact not_nonempty_smallestConcreteSourceDependency
    (nonempty_smallestConcreteSourceDependency_of_nonempty_concreteLowerTables H)

theorem not_nonempty_concreteReducedMetricCertificate :
    Not (Nonempty ConcreteReducedMetricCertificate) := by
  intro H
  cases H with
  | intro C =>
      exact not_nonempty_concreteLowerTables
        (Nonempty.intro C.lowerTables)

/-- Final blocker theorem for W27: the concrete lower-table route would close
both Pach-Toth endpoints, but it cannot be used as an unconditional final
theorem because its smallest concrete dependency, `PeriodSearchData`, is
uninhabited in the current source tree. -/
theorem noFakeFinalBlocker_smallestConcreteSourceDependency :
    Not (Nonempty SmallestConcreteSourceDependency) /\
      Not (Nonempty ConcreteNonConnectorLowerTableFamily) /\
        (Nonempty ConcreteNonConnectorLowerTableFamily ->
          ExactAndArbitraryTargets) :=
  And.intro not_nonempty_smallestConcreteSourceDependency
    (And.intro not_nonempty_concreteLowerTables
      exactAndArbitraryTargets_of_nonempty_concreteLowerTables)

/-- The positive exact-chain route is likewise still blocked exactly by the
large exact-block tail after the checked one-through-five small blocks. -/
theorem positiveExactChainPackage_blocker :
    Iff (Nonempty PositiveExactChainPackage)
      (PositiveExactChainPackageW26.ExactBlocksOneThroughFive /\
        RemainingPositiveExactChainBlocker) :=
  PositiveExactChainPackageW26.remainingBlocker_is_largeExactBlockTail_after_small_blocks

end

end PachTothW27FinalAssembly
end PachToth

namespace Verified

abbrev PachTothW27SmallestConcreteSourceDependency : Type :=
  PachToth.PachTothW27FinalAssembly.SmallestConcreteSourceDependency

abbrev PachTothW27FinalConcreteNonConnectorLowerTableFamily : Type :=
  PachToth.PachTothW27FinalAssembly.ConcreteNonConnectorLowerTableFamily

theorem pachtoth_w27_noFakeFinalBlocker_smallestConcreteSourceDependency :
    Not (Nonempty PachTothW27SmallestConcreteSourceDependency) /\
      Not (Nonempty PachTothW27FinalConcreteNonConnectorLowerTableFamily) /\
        (Nonempty PachTothW27FinalConcreteNonConnectorLowerTableFamily ->
          PachToth.PachTothW27FinalAssembly.ExactAndArbitraryTargets) :=
  PachToth.PachTothW27FinalAssembly.noFakeFinalBlocker_smallestConcreteSourceDependency

theorem pachtoth_w27_exactAndArbitraryTargets_iff_smallestExactSourcePackage :
    PachToth.PachTothW27FinalAssembly.ExactAndArbitraryTargets <->
      Nonempty PachToth.PachTothW27FinalAssembly.SmallestExactSourcePackage :=
  PachToth.PachTothW27FinalAssembly.exactAndArbitraryTargets_iff_smallestExactSourcePackage

end Verified
end ErdosProblems1066
