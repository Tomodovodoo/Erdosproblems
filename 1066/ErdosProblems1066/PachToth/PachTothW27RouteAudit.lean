import ErdosProblems1066.PachToth.ArbitraryNFinalAssemblyW26
import ErdosProblems1066.PachToth.ClosedPlacementConcreteConstructionW26
import ErdosProblems1066.PachToth.ConcreteReducedMetricCertificatesW26
import ErdosProblems1066.PachToth.ExactTargetClosureW26
import ErdosProblems1066.PachToth.NonRoleSplitSourceConstructionW26
import ErdosProblems1066.PachToth.PachTothW26RouteAudit

set_option autoImplicit false

/-!
# W27 Pach-Toth route audit

Findings:

* The W26 route contains an intentional target-to-source equivalence around
  `ExactTarget <-> Nonempty PositiveExactChainPackage`.  This is useful as a
  closure characterization, but it is not a concrete source endpoint.
* The arbitrary-`n` target is equivalent to the exact target, so it should not
  be presented as an independent unconditional closure.
* The meaningful concrete-source fronts currently available are the concrete
  non-connector lower-table route, its reduced-metric certificate wrapper, and
  the concrete closed-orbit family route.
* No public `KnownBounds` theorem is exposed here.  Any route through the
  generated closure metric package remains conditional on concrete source data.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW27RouteAudit

noncomputable section

/-! ## Shared target vocabulary -/

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

/-! ## Concrete lower-table route -/

abbrev ConcreteLowerTableFamily : Type :=
  ConcreteReducedMetricCertificatesW26.ConcreteNonConnectorLowerTableFamily

abbrev ConcreteLowerTableGate : Prop :=
  Nonempty ConcreteLowerTableFamily

abbrev ConcreteReducedMetricCertificate : Type :=
  ConcreteReducedMetricCertificatesW26.ConcreteReducedMetricCertificate

abbrev ConcreteReducedMetricCertificateGate : Prop :=
  Nonempty ConcreteReducedMetricCertificate

abbrev DirectFullMetricSourcePackage : Type :=
  PachTothW26RouteAudit.DirectFullMetricSourcePackage

abbrev DirectFullMetricSourceGate : Prop :=
  Nonempty DirectFullMetricSourcePackage

theorem concreteReducedMetricCertificateGate_iff_concreteLowerTableGate :
    ConcreteReducedMetricCertificateGate <-> ConcreteLowerTableGate :=
  ConcreteReducedMetricCertificatesW26.nonempty_concreteReducedMetricCertificate_iff_lowerTables

theorem directFullMetricSourceGate_iff_concreteLowerTableGate :
    DirectFullMetricSourceGate <-> ConcreteLowerTableGate :=
  PachTothW26RouteAudit.directFullMetricSourceGate_iff_concreteLowerTableGate

theorem concreteLowerTableGate_iff_directFullMetricSourceGate :
    ConcreteLowerTableGate <-> DirectFullMetricSourceGate :=
  directFullMetricSourceGate_iff_concreteLowerTableGate.symm

theorem exactTarget_of_concreteLowerTableGate
    (H : ConcreteLowerTableGate) :
    ExactTarget :=
  ConcreteReducedMetricCertificatesW26.exactTarget_of_nonempty_concreteLowerTables
    H

theorem arbitraryTarget_of_concreteLowerTableGate
    (H : ConcreteLowerTableGate) :
    ArbitraryTarget :=
  ConcreteReducedMetricCertificatesW26.arbitraryTarget_of_nonempty_concreteLowerTables
    H

theorem exactAndArbitraryTargets_of_concreteLowerTableGate
    (H : ConcreteLowerTableGate) :
    ExactTarget /\ ArbitraryTarget :=
  And.intro
    (exactTarget_of_concreteLowerTableGate H)
    (arbitraryTarget_of_concreteLowerTableGate H)

theorem exactAndArbitraryTargets_of_concreteReducedMetricCertificateGate
    (H : ConcreteReducedMetricCertificateGate) :
    ExactTarget /\ ArbitraryTarget :=
  exactAndArbitraryTargets_of_concreteLowerTableGate
    (concreteReducedMetricCertificateGate_iff_concreteLowerTableGate.mp H)

/-! ## Generated closure handoff, kept conditional and non-public -/

abbrev GeneratedClosureMetricRowPackage : Type :=
  ConcreteReducedMetricCertificatesW26.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricRowPackageGate : Prop :=
  Nonempty GeneratedClosureMetricRowPackage

theorem generatedClosureMetricRowPackageGate_of_concreteLowerTableGate
    (H : ConcreteLowerTableGate) :
    GeneratedClosureMetricRowPackageGate :=
  ConcreteReducedMetricCertificatesW26.nonempty_generatedClosureMetricRowPackage_of_nonempty_concreteLowerTables
    H

/-! ## Concrete closed-orbit route -/

abbrev ConcreteClosedOrbitFamily : Type :=
  ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily

abbrev ConcreteClosedOrbitFamilyGate : Prop :=
  Nonempty ConcreteClosedOrbitFamily

abbrev MinimalFieldsWithOrbitClosure : Type :=
  ClosedPlacementConcreteConstructionW26.MinimalFieldsWithOrbitClosure

abbrev MinimalFieldsWithOrbitClosureGate : Prop :=
  Nonempty MinimalFieldsWithOrbitClosure

theorem concreteClosedOrbitFamilyGate_iff_minimalFieldsWithOrbitClosureGate :
    ConcreteClosedOrbitFamilyGate <-> MinimalFieldsWithOrbitClosureGate :=
  ClosedPlacementConcreteConstructionW26.nonempty_concreteClosedOrbitFamily_iff_minimalFieldsWithOrbitClosure

theorem exactTarget_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    ExactTarget :=
  ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily.exactTarget_of_nonempty
    H

theorem arbitraryTarget_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    ArbitraryTarget :=
  ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily.arbitraryTarget_of_nonempty
    H

theorem exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    ExactTarget /\ ArbitraryTarget :=
  And.intro
    (exactTarget_of_concreteClosedOrbitFamilyGate H)
    (arbitraryTarget_of_concreteClosedOrbitFamilyGate H)

/-! ## Target-to-source cycle findings -/

abbrev PositiveExactChainPackage : Type :=
  ExactTargetClosureW26.SmallestExactSourcePackage

abbrev PositiveExactChainPackageGate : Prop :=
  Nonempty PositiveExactChainPackage

abbrev NonRoleSplitSource : Type :=
  NonRoleSplitSourceConstructionW26.NonRoleSplitSource

abbrev NonRoleSplitSourceGate : Prop :=
  Nonempty NonRoleSplitSource

abbrev W11ExactClosedChainPackage : Type :=
  NonRoleSplitSourceConstructionW26.W11ExactClosedChainPackage

abbrev W11ExactClosedChainPackageGate : Prop :=
  Nonempty W11ExactClosedChainPackage

theorem audit_exactTarget_iff_positiveExactChainPackageGate :
    ExactTarget <-> PositiveExactChainPackageGate :=
  ExactTargetClosureW26.exactTarget_iff_nonempty_smallestExactSourcePackage

theorem audit_positiveExactChainPackageGate_of_exactTarget
    (H : ExactTarget) :
    PositiveExactChainPackageGate :=
  audit_exactTarget_iff_positiveExactChainPackageGate.mp H

theorem audit_exactTarget_of_positiveExactChainPackageGate
    (H : PositiveExactChainPackageGate) :
    ExactTarget :=
  audit_exactTarget_iff_positiveExactChainPackageGate.mpr H

theorem audit_arbitraryTarget_iff_exactTarget :
    ArbitraryTarget <-> ExactTarget :=
  ArbitraryNFinalAssemblyW26.arbitraryTarget_iff_exactTarget

theorem audit_nonRoleSplitSourceGate_iff_w11ExactClosedChainPackageGate :
    NonRoleSplitSourceGate <-> W11ExactClosedChainPackageGate :=
  NonRoleSplitSourceConstructionW26.nonempty_nonRoleSplitSource_iff_w11ExactClosedChainPackage

end

end PachTothW27RouteAudit
end PachToth

namespace Verified

abbrev PachTothW27ConcreteLowerTableGate : Prop :=
  PachToth.PachTothW27RouteAudit.ConcreteLowerTableGate

abbrev PachTothW27ConcreteReducedMetricCertificateGate : Prop :=
  PachToth.PachTothW27RouteAudit.ConcreteReducedMetricCertificateGate

abbrev PachTothW27ConcreteClosedOrbitFamilyGate : Prop :=
  PachToth.PachTothW27RouteAudit.ConcreteClosedOrbitFamilyGate

theorem pachtoth_w27_concreteReducedMetricCertificateGate_iff_concreteLowerTableGate :
    PachTothW27ConcreteReducedMetricCertificateGate <->
      PachTothW27ConcreteLowerTableGate :=
  PachToth.PachTothW27RouteAudit.concreteReducedMetricCertificateGate_iff_concreteLowerTableGate

theorem pachtoth_w27_exactAndArbitraryTargets_of_concreteLowerTableGate
    (H : PachTothW27ConcreteLowerTableGate) :
    PachToth.PachTothW27RouteAudit.ExactTarget /\
      PachToth.PachTothW27RouteAudit.ArbitraryTarget :=
  PachToth.PachTothW27RouteAudit.exactAndArbitraryTargets_of_concreteLowerTableGate
    H

theorem pachtoth_w27_exactAndArbitraryTargets_of_concreteReducedMetricCertificateGate
    (H : PachTothW27ConcreteReducedMetricCertificateGate) :
    PachToth.PachTothW27RouteAudit.ExactTarget /\
      PachToth.PachTothW27RouteAudit.ArbitraryTarget :=
  PachToth.PachTothW27RouteAudit.exactAndArbitraryTargets_of_concreteReducedMetricCertificateGate
    H

theorem pachtoth_w27_exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate
    (H : PachTothW27ConcreteClosedOrbitFamilyGate) :
    PachToth.PachTothW27RouteAudit.ExactTarget /\
      PachToth.PachTothW27RouteAudit.ArbitraryTarget :=
  PachToth.PachTothW27RouteAudit.exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate
    H

end Verified
end ErdosProblems1066
