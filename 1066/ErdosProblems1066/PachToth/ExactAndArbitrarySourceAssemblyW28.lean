import ErdosProblems1066.PachToth.FreePlacementFieldsConcreteW27
import ErdosProblems1066.PachToth.PachTothW27FinalAssembly
import ErdosProblems1066.PachToth.PachTothW27RouteAudit
import ErdosProblems1066.PachToth.PositiveExactChainAssemblyW27
import ErdosProblems1066.PachToth.RemainderExactSourceConstructionW27

set_option autoImplicit false

/-!
# W28 exact/arbitrary Pach-Toth source assembly

This leaf collects only source-to-target handoffs for the Pach-Toth endpoint.
It gives no public known-bound wrapper and does not build a source from an
endpoint statement.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactAndArbitrarySourceAssemblyW28

noncomputable section

/-! ## Endpoint vocabulary -/

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev ExactAndArbitraryTargets : Prop :=
  ExactTarget /\ ArbitraryTarget

/-! ## Permitted source packages and gates -/

abbrev NonRoleSplitSource : Type :=
  PositiveExactChainAssemblyW27.NonRoleSplitSource

abbrev PositiveExactChainSource : Type :=
  PositiveExactChainAssemblyW27.ExposedExactChainSource

abbrev PositiveExactChainPackage : Type :=
  PositiveExactChainAssemblyW27.PositiveExactChainPackage

abbrev RemainderExactSourcePackage : Type :=
  RemainderExactSourceConstructionW27.RemainderExactSourcePackage

abbrev ConcreteClosedOrbitFamily : Type :=
  FreePlacementFieldsConcreteW27.ConcreteClosedOrbitFamily

abbrev NonRoleSplitSourceGate : Prop :=
  Nonempty NonRoleSplitSource

abbrev PositiveExactChainSourceGate : Prop :=
  Nonempty PositiveExactChainSource

abbrev PositiveExactChainPackageGate : Prop :=
  Nonempty PositiveExactChainPackage

abbrev RemainderExactSourceGate : Prop :=
  Nonempty RemainderExactSourcePackage

abbrev ConcreteClosedOrbitFamilyGate : Prop :=
  Nonempty ConcreteClosedOrbitFamily

abbrev SourceGate : Prop :=
  NonRoleSplitSourceGate \/
    PositiveExactChainSourceGate \/
      RemainderExactSourceGate \/
        ConcreteClosedOrbitFamilyGate

/-! ## Positive exact-chain source -/

def positiveExactChainPackageOfSource
    (S : PositiveExactChainSource) :
    PositiveExactChainPackage :=
  PositiveExactChainAssemblyW27.packageOfExposedExactChainSource S

theorem exactTarget_of_positiveExactChainPackage
    (P : PositiveExactChainPackage) :
    ExactTarget :=
  PositiveExactChainPackageW26.exactTarget_of_package P

theorem arbitraryTarget_of_positiveExactChainPackage
    (P : PositiveExactChainPackage) :
    ArbitraryTarget :=
  ArbitraryNFinalAssemblyW26.arbitraryTarget_of_positiveExactChainPackage P

theorem exactAndArbitraryTargets_of_positiveExactChainPackage
    (P : PositiveExactChainPackage) :
    ExactAndArbitraryTargets :=
  And.intro
    (exactTarget_of_positiveExactChainPackage P)
    (arbitraryTarget_of_positiveExactChainPackage P)

theorem exactAndArbitraryTargets_of_positiveExactChainSource
    (S : PositiveExactChainSource) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_positiveExactChainPackage
    (positiveExactChainPackageOfSource S)

theorem exactAndArbitraryTargets_of_positiveExactChainSourceGate
    (H : PositiveExactChainSourceGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | intro S =>
      exact exactAndArbitraryTargets_of_positiveExactChainSource S

theorem exactAndArbitraryTargets_of_positiveExactChainPackageGate
    (H : PositiveExactChainPackageGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | intro P =>
      exact exactAndArbitraryTargets_of_positiveExactChainPackage P

/-! ## Non-role split source -/

def positiveExactChainSourceOfNonRoleSplitSource
    (S : NonRoleSplitSource) :
    PositiveExactChainSource :=
  PositiveExactChainAssemblyW27.exposedExactChainSourceOfMinimal
    (NonRoleSplitSourceConstructionW26.w11ExactClosedChainPackageOfNonRoleSplitSource
      S)

theorem positiveExactChainSourceGate_of_nonRoleSplitSourceGate
    (H : NonRoleSplitSourceGate) :
    PositiveExactChainSourceGate := by
  cases H with
  | intro S =>
      exact
        Nonempty.intro
          (positiveExactChainSourceOfNonRoleSplitSource S)

theorem exactAndArbitraryTargets_of_nonRoleSplitSource
    (S : NonRoleSplitSource) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_positiveExactChainSource
    (positiveExactChainSourceOfNonRoleSplitSource S)

theorem exactAndArbitraryTargets_of_nonRoleSplitSourceGate
    (H : NonRoleSplitSourceGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | intro S =>
      exact exactAndArbitraryTargets_of_nonRoleSplitSource S

/-! ## Remainder exact source -/

theorem exactTarget_of_remainderExactSourcePackage
    (S : RemainderExactSourcePackage) :
    ExactTarget :=
  PositiveExactChainPackageW26.exactTarget_of_package S.exact

theorem arbitraryTarget_of_remainderExactSourcePackage
    (S : RemainderExactSourcePackage) :
    ArbitraryTarget :=
  RemainderExactSourceConstructionW27.arbitraryTarget_of_package S

theorem exactAndArbitraryTargets_of_remainderExactSourcePackage
    (S : RemainderExactSourcePackage) :
    ExactAndArbitraryTargets :=
  And.intro
    (exactTarget_of_remainderExactSourcePackage S)
    (arbitraryTarget_of_remainderExactSourcePackage S)

theorem exactAndArbitraryTargets_of_remainderExactSourceGate
    (H : RemainderExactSourceGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | intro S =>
      exact exactAndArbitraryTargets_of_remainderExactSourcePackage S

theorem remainderExactSourceGate_of_positiveExactChainPackageGate
    (H : PositiveExactChainPackageGate) :
    RemainderExactSourceGate :=
  RemainderExactSourceConstructionW27.nonempty_package_iff_exactSource.mpr H

/-! ## Concrete closed orbit family -/

theorem exactTarget_of_concreteClosedOrbitFamily
    (F : ConcreteClosedOrbitFamily) :
    ExactTarget :=
  ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily.exactTarget F

theorem arbitraryTarget_of_concreteClosedOrbitFamily
    (F : ConcreteClosedOrbitFamily) :
    ArbitraryTarget :=
  ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily.arbitraryTarget F

theorem exactAndArbitraryTargets_of_concreteClosedOrbitFamily
    (F : ConcreteClosedOrbitFamily) :
    ExactAndArbitraryTargets :=
  And.intro
    (exactTarget_of_concreteClosedOrbitFamily F)
    (arbitraryTarget_of_concreteClosedOrbitFamily F)

theorem exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | intro F =>
      exact exactAndArbitraryTargets_of_concreteClosedOrbitFamily F

/-! ## Unified gate -/

theorem exactAndArbitraryTargets_of_sourceGate
    (H : SourceGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | inl hNonRole =>
      exact exactAndArbitraryTargets_of_nonRoleSplitSourceGate hNonRole
  | inr hRest =>
      cases hRest with
      | inl hPositive =>
          exact exactAndArbitraryTargets_of_positiveExactChainSourceGate hPositive
      | inr hRest =>
          cases hRest with
          | inl hRemainder =>
              exact exactAndArbitraryTargets_of_remainderExactSourceGate hRemainder
          | inr hClosedOrbit =>
              exact exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate hClosedOrbit

theorem exactAndArbitraryTargets_of_w27_concreteClosedOrbitGate
    (H : PachTothW27RouteAudit.ConcreteClosedOrbitFamilyGate) :
    ExactAndArbitraryTargets :=
  PachTothW27RouteAudit.exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate
    H

theorem exactAndArbitraryTargets_of_w27_remainderExactSourceGate
    (H : Nonempty RemainderExactSourceConstructionW27.RemainderExactSourcePackage) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_remainderExactSourceGate H

end

end ExactAndArbitrarySourceAssemblyW28
end PachToth

namespace Verified

abbrev PachTothW28ExactAndArbitrarySourceGate : Prop :=
  PachToth.ExactAndArbitrarySourceAssemblyW28.SourceGate

theorem pachtoth_w28_exactAndArbitraryTargets_of_sourceGate
    (H : PachTothW28ExactAndArbitrarySourceGate) :
    PachToth.ExactAndArbitrarySourceAssemblyW28.ExactAndArbitraryTargets :=
  PachToth.ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_sourceGate
    H

theorem pachtoth_w28_exactAndArbitraryTargets_of_nonRoleSplitSourceGate
    (H :
      PachToth.ExactAndArbitrarySourceAssemblyW28.NonRoleSplitSourceGate) :
    PachToth.ExactAndArbitrarySourceAssemblyW28.ExactAndArbitraryTargets :=
  PachToth.ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_nonRoleSplitSourceGate
    H

theorem pachtoth_w28_exactAndArbitraryTargets_of_positiveExactChainSourceGate
    (H :
      PachToth.ExactAndArbitrarySourceAssemblyW28.PositiveExactChainSourceGate) :
    PachToth.ExactAndArbitrarySourceAssemblyW28.ExactAndArbitraryTargets :=
  PachToth.ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_positiveExactChainSourceGate
    H

theorem pachtoth_w28_exactAndArbitraryTargets_of_remainderExactSourceGate
    (H :
      PachToth.ExactAndArbitrarySourceAssemblyW28.RemainderExactSourceGate) :
    PachToth.ExactAndArbitrarySourceAssemblyW28.ExactAndArbitraryTargets :=
  PachToth.ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_remainderExactSourceGate
    H

theorem pachtoth_w28_exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate
    (H :
      PachToth.ExactAndArbitrarySourceAssemblyW28.ConcreteClosedOrbitFamilyGate) :
    PachToth.ExactAndArbitrarySourceAssemblyW28.ExactAndArbitraryTargets :=
  PachToth.ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate
    H

end Verified
end ErdosProblems1066
