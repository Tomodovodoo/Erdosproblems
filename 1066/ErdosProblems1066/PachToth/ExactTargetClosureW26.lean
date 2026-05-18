import ErdosProblems1066.PachToth.DirectFullMetricSourceInhabitationW25
import ErdosProblems1066.PachToth.FreePlacementFieldsInhabitationW25
import ErdosProblems1066.PachToth.NonRoleSplitSourceInhabitationW25

set_option autoImplicit false

/-!
# W26 exact Pach--Toth target closure

This file checks the W25 direct/free/non-role source surfaces against the
exact Pach--Toth `5 / 16` target.  No unconditional inhabitant of the source
data is present in the current tree, so the tight closure is the exact iff
with the smallest existing source package: positive exact-chain certificates
for every positive block count.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactTargetClosureW26

noncomputable section

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev SmallestExactSourcePackage : Type :=
  NonRoleSplitSourceInhabitationW25.PositiveExactChainPackage

abbrev NonRoleSplitSource : Type :=
  NonRoleSplitSourceInhabitationW25.NonRoleSplitSource

abbrev MinimalFreePlacementFields : Type :=
  FreePlacementFieldsInhabitationW25.MinimalFreePlacementFields

abbrev ExplicitEdgeSoundnessFamily : Type :=
  FreePlacementFieldsInhabitationW25.ExplicitEdgeSoundnessFamily

abbrev DirectFullMetricSourcePackage : Type :=
  DirectFullMetricSourceInhabitationW25.DirectFullMetricSourcePackage

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  DirectFullMetricSourceInhabitationW25.ConcreteNonConnectorLowerTableFamily

abbrev ConcreteValueMatrixRowPackage : Type :=
  DirectFullMetricSourceInhabitationW25.ConcreteValueMatrixRowPackage

/-! ## Tight exact-target closure -/

/-- The exact target is equivalent to the smallest currently exposed source:
positive exact-chain certificates for every positive block count. -/
theorem exactTarget_iff_nonempty_smallestExactSourcePackage :
    ExactTarget <-> Nonempty SmallestExactSourcePackage :=
  Iff.trans
    NonRoleSplitSourceInhabitationW25.nonempty_nonRoleSplitSource_iff_exactTarget.symm
    NonRoleSplitSourceInhabitationW25.nonempty_nonRoleSplitSource_iff_positiveExactChainPackage

theorem exactTarget_of_smallestExactSourcePackage
    (P : SmallestExactSourcePackage) :
    ExactTarget :=
  exactTarget_iff_nonempty_smallestExactSourcePackage.mpr
    (Nonempty.intro P)

theorem nonempty_smallestExactSourcePackage_of_exactTarget
    (H : ExactTarget) :
    Nonempty SmallestExactSourcePackage :=
  exactTarget_iff_nonempty_smallestExactSourcePackage.mp H

/-! ## W25 source-to-target closures -/

theorem exactTarget_of_nonRoleSplitSource
    (S : NonRoleSplitSource) :
    ExactTarget :=
  NonRoleSplitSourceInhabitationW25.exactTarget_of_nonRoleSplitSource S

theorem exactTarget_of_minimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    ExactTarget :=
  NonRoleSplitSourceInhabitationW25.exactTarget_of_freePlacementSourceFields S

theorem exactTarget_of_explicitEdgeSoundnessFamily
    (G : ExplicitEdgeSoundnessFamily) :
    ExactTarget :=
  open FreePlacementFieldsInhabitationW25 in
  targetUpperConstructionFiveSixteen_of_explicitEdgeSoundnessFamily G

theorem exactTarget_of_directFullMetricSourcePackage
    (P : DirectFullMetricSourcePackage) :
    ExactTarget :=
  DirectFullMetricSourceInhabitationW25.targetUpperConstructionFiveSixteen_of_directPackage
    P

theorem exactTarget_of_concreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    ExactTarget :=
  DirectFullMetricSourceInhabitationW25.targetUpperConstructionFiveSixteen_of_concreteLowerTables
    C

theorem exactTarget_of_concreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    ExactTarget :=
  DirectFullMetricSourceInhabitationW25.targetUpperConstructionFiveSixteen_of_rowPackage
    P

/-! ## W25 sources also collapse back to the smallest exact source -/

theorem nonempty_smallestExactSourcePackage_of_nonRoleSplitSource
    (S : NonRoleSplitSource) :
    Nonempty SmallestExactSourcePackage :=
  nonempty_smallestExactSourcePackage_of_exactTarget
    (exactTarget_of_nonRoleSplitSource S)

theorem nonempty_smallestExactSourcePackage_of_minimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    Nonempty SmallestExactSourcePackage :=
  nonempty_smallestExactSourcePackage_of_exactTarget
    (exactTarget_of_minimalFreePlacementFields S)

theorem nonempty_smallestExactSourcePackage_of_directFullMetricSourcePackage
    (P : DirectFullMetricSourcePackage) :
    Nonempty SmallestExactSourcePackage :=
  nonempty_smallestExactSourcePackage_of_exactTarget
    (exactTarget_of_directFullMetricSourcePackage P)

end

end ExactTargetClosureW26
end PachToth

namespace Verified

abbrev PachTothW26SmallestExactSourcePackage : Type :=
  PachToth.ExactTargetClosureW26.SmallestExactSourcePackage

theorem pachtoth_w26_exactTarget_iff_smallestExactSourcePackage :
    PachToth.targetUpperConstructionFiveSixteen <->
      Nonempty PachTothW26SmallestExactSourcePackage :=
  PachToth.ExactTargetClosureW26.exactTarget_iff_nonempty_smallestExactSourcePackage

end Verified
end ErdosProblems1066
