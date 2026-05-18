import ErdosProblems1066.PachToth.PachTothW23RouteAudit
import ErdosProblems1066.PachToth.PachTothKnownBoundsFromConcreteRowsW23
import ErdosProblems1066.PachToth.ConcreteValueMatrixRowPackageInhabitationW23
import ErdosProblems1066.PachToth.CandidateValueMatrixRowPackageInhabitationW23
import ErdosProblems1066.PachToth.PeriodBaseFixingSourceInhabitationW23
import ErdosProblems1066.PachToth.ConcreteCrossBlockFamilyInhabitationW23
import ErdosProblems1066.PachToth.RemainingSeparationConcreteW23
import ErdosProblems1066.PachToth.ExactBaseFullMetricConcreteW23

set_option autoImplicit false

/-!
# W24 Pach-Toth route audit

This module is an audit layer only.  It records CI-facing declarations for the
current W23/W24 route state without adding any unconditional Pach-Toth
endpoint.  In particular, endpoint theorems remain gated by row packages or by
the non-role direct-source package named below.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW24RouteAudit

noncomputable section

/-! ## W23 route gates -/

abbrev KnownBoundsGate : Prop :=
  PachTothW23RouteAudit.KnownBoundsGate

abbrev KnownBoundsStatements : Prop :=
  PachTothW23RouteAudit.KnownBoundsStatements

abbrev FinalConditionalGate : Prop :=
  PachTothW23RouteAudit.FinalConditionalGate

abbrev ExactBlockBound (k : Nat) : Prop :=
  PachTothW23RouteAudit.ExactBlockBound k

abbrev ArbitraryBound (n : Nat) : Prop :=
  PachTothW23RouteAudit.ArbitraryBound n

theorem finalConditionalGate_iff_knownBoundsGate :
    FinalConditionalGate <-> KnownBoundsGate :=
  PachTothW23RouteAudit.finalConditionalGate_iff_knownBoundsGate

/-! ## Row-gated endpoints -/

abbrev ExactTarget : Prop :=
  PachTothKnownBoundsFromConcreteRowsW23.ExactTarget

abbrev ArbitraryTarget : Prop :=
  PachTothKnownBoundsFromConcreteRowsW23.ArbitraryTarget

abbrev FixedTarget (n : Nat) : Prop :=
  PachTothKnownBoundsFromConcreteRowsW23.FixedTarget n

abbrev ConcreteValueMatrixRowPackage : Type :=
  PachTothKnownBoundsFromConcreteRowsW23.ConcreteValueMatrixRowPackage

abbrev CandidateValueMatrixRowPackage : Type :=
  PachTothKnownBoundsFromConcreteRowsW23.CandidateValueMatrixRowPackage

abbrev ConcreteRowsEndpointPackage : Type :=
  PachTothKnownBoundsFromConcreteRowsW23.ConcreteRowsEndpointPackage

abbrev CandidateRowsEndpointPackage : Type :=
  PachTothKnownBoundsFromConcreteRowsW23.CandidateRowsEndpointPackage

abbrev ConcreteRowsEndpointGate : Prop :=
  Nonempty ConcreteValueMatrixRowPackage

abbrev CandidateRowsEndpointGate : Prop :=
  Nonempty CandidateValueMatrixRowPackage

theorem concreteRowsEndpointGate_iff_endpointPackage :
    ConcreteRowsEndpointGate <-> Nonempty ConcreteRowsEndpointPackage :=
  PachTothKnownBoundsFromConcreteRowsW23.nonempty_concreteRowsEndpointPackage_iff_rowPackage.symm

theorem candidateRowsEndpointGate_iff_endpointPackage :
    CandidateRowsEndpointGate <-> Nonempty CandidateRowsEndpointPackage :=
  PachTothKnownBoundsFromConcreteRowsW23.nonempty_candidateRowsEndpointPackage_iff_rowPackage.symm

theorem exactTarget_of_concreteRowsEndpointGate
    (H : ConcreteRowsEndpointGate) :
    ExactTarget :=
  PachTothKnownBoundsFromConcreteRowsW23.targetUpperConstructionFiveSixteen_of_nonempty_concreteValueMatrixRowPackage
    H

theorem arbitraryTarget_of_concreteRowsEndpointGate
    (H : ConcreteRowsEndpointGate) :
    ArbitraryTarget :=
  PachTothKnownBoundsFromConcreteRowsW23.targetUpperConstructionFiveSixteenArbitrary_of_nonempty_concreteValueMatrixRowPackage
    H

theorem fixedTarget_of_concreteRowsEndpointGate
    (H : ConcreteRowsEndpointGate) (n : Nat) :
    FixedTarget n :=
  arbitraryTarget_of_concreteRowsEndpointGate H n

theorem upper_bound_five_sixteen_exact_of_concreteRowsEndpointGate
    (H : ConcreteRowsEndpointGate) (k : Nat) (hk : 0 < k) :
    PachTothKnownBoundsFromConcreteRowsW23.ExactBlockBound k :=
  PachTothKnownBoundsFromConcreteRowsW23.upper_bound_five_sixteen_exact_of_nonempty_concreteValueMatrixRowPackage
    H k hk

theorem upper_bound_five_sixteen_arbitrary_of_concreteRowsEndpointGate
    (H : ConcreteRowsEndpointGate) (n : Nat) :
    PachTothKnownBoundsFromConcreteRowsW23.ArbitraryBound n :=
  PachTothKnownBoundsFromConcreteRowsW23.upper_bound_five_sixteen_arbitrary_of_nonempty_concreteValueMatrixRowPackage
    H n

theorem exactTarget_of_candidateRowsEndpointGate
    (H : CandidateRowsEndpointGate) :
    ExactTarget :=
  PachTothKnownBoundsFromConcreteRowsW23.targetUpperConstructionFiveSixteen_of_nonempty_candidateValueMatrixRowPackage
    H

theorem arbitraryTarget_of_candidateRowsEndpointGate
    (H : CandidateRowsEndpointGate) :
    ArbitraryTarget :=
  PachTothKnownBoundsFromConcreteRowsW23.targetUpperConstructionFiveSixteenArbitrary_of_nonempty_candidateValueMatrixRowPackage
    H

theorem fixedTarget_of_candidateRowsEndpointGate
    (H : CandidateRowsEndpointGate) (n : Nat) :
    FixedTarget n :=
  arbitraryTarget_of_candidateRowsEndpointGate H n

theorem upper_bound_five_sixteen_exact_of_candidateRowsEndpointGate
    (H : CandidateRowsEndpointGate) (k : Nat) (hk : 0 < k) :
    PachTothKnownBoundsFromConcreteRowsW23.ExactBlockBound k :=
  PachTothKnownBoundsFromConcreteRowsW23.upper_bound_five_sixteen_exact_of_nonempty_candidateValueMatrixRowPackage
    H k hk

theorem upper_bound_five_sixteen_arbitrary_of_candidateRowsEndpointGate
    (H : CandidateRowsEndpointGate) (n : Nat) :
    PachTothKnownBoundsFromConcreteRowsW23.ArbitraryBound n :=
  PachTothKnownBoundsFromConcreteRowsW23.upper_bound_five_sixteen_arbitrary_of_nonempty_candidateValueMatrixRowPackage
    H n

theorem knownBoundsGate_of_concreteRowsEndpointGate
    (H : ConcreteRowsEndpointGate) :
    KnownBoundsGate := by
  cases H with
  | intro P =>
      exact PachTothW23RouteAudit.knownBoundsGate_of_concreteValueMatrixRowPackage
        P

/-! ## Blocked role-hinge and base-fixing paths -/

abbrev RoleHingeTransitions : Type :=
  PachTothW23RouteAudit.RoleHingeTransitions

abbrev RoleHingeSourceFields (T : RoleHingeTransitions) :=
  PachTothW23RouteAudit.RoleHingeSourceFields T

abbrev BaseFixingAlternative (T : RoleHingeTransitions) : Prop :=
  PachTothW23RouteAudit.BaseFixingAlternative T

abbrev MissingBaseFixingRows (T : RoleHingeTransitions) : Prop :=
  PeriodBaseFixingSourceInhabitationW23.MissingBaseFixingRows T

abbrev RoleHingedPeriodSearchFamily : Type :=
  PachTothW23RouteAudit.RoleHingedPeriodSearchFamily

theorem roleHingeSourceFields_iff_baseFixingAlternative
    (T : RoleHingeTransitions) :
    Nonempty (RoleHingeSourceFields T) <-> BaseFixingAlternative T :=
  PachTothW23RouteAudit.roleHingeSourceFields_iff_baseFixingAlternative T

theorem no_roleHingePeriodEquationRows :
    Not (Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T)) :=
  PachTothW23RouteAudit.no_roleHingePeriodEquationRows

theorem no_roleHingedPeriodSearchFamily :
    Not (Nonempty RoleHingedPeriodSearchFamily) :=
  PachTothW23RouteAudit.no_roleHingedPeriodSearchFamily

theorem missingBaseFixingRows_of_roleHingeTransitions
    (T : RoleHingeTransitions) :
    MissingBaseFixingRows T :=
  PeriodBaseFixingSourceInhabitationW23.missingBaseFixingRows_of_roleHingeTransitions
    T

theorem not_baseFixingAlternative_of_roleHingeTransitions
    (T : RoleHingeTransitions) :
    Not (BaseFixingAlternative T) :=
  PeriodBaseFixingSourceInhabitationW23.not_baseFixingAlternative_of_roleHingeTransitions
    T

theorem not_roleHingeSourceFields_of_roleHingeTransitions
    (T : RoleHingeTransitions) :
    RoleHingeSourceFields T -> False :=
  PeriodBaseFixingSourceInhabitationW23.not_sourceFields_of_roleHingeTransitions
    T

theorem no_concreteValueMatrixRows :
    Not ConcreteRowsEndpointGate :=
  ConcreteValueMatrixRowPackageInhabitationW23.not_nonempty_rowPackage

theorem no_candidateValueMatrixRows :
    Not CandidateRowsEndpointGate :=
  CandidateValueMatrixRowPackageInhabitationW23.not_nonempty_candidateValueMatrixRowPackage

theorem no_concreteValueMatrixEndpointPackage :
    Not (Nonempty ConcreteRowsEndpointPackage) := by
  intro H
  exact no_concreteValueMatrixRows
    (concreteRowsEndpointGate_iff_endpointPackage.2 H)

theorem no_candidateValueMatrixEndpointPackage :
    Not (Nonempty CandidateRowsEndpointPackage) := by
  intro H
  exact no_candidateValueMatrixRows
    (candidateRowsEndpointGate_iff_endpointPackage.2 H)

/-! ## Non-role direct-source remaining package -/

abbrev GeneratedChainFamily : Type :=
  PachTothW23RouteAudit.GeneratedChainFamily

abbrev ClosureSource (F : GeneratedChainFamily) :=
  PachTothW23RouteAudit.ClosureSource F

abbrev ReducedMetricFields (F : GeneratedChainFamily) :=
  PachTothW23RouteAudit.ReducedMetricFields F

abbrev GeneratedClosureMetricRowPackage : Type :=
  PachTothW23RouteAudit.GeneratedClosureMetricRowPackage

/-- The current non-role direct-source obligation: one generated family with
closure rows and reduced metric rows for that same family. -/
structure NonRoleDirectSourceMissingPackage where
  family : GeneratedChainFamily
  closureSource : ClosureSource family
  reducedMetric : ReducedMetricFields family

namespace NonRoleDirectSourceMissingPackage

def toGeneratedClosureMetricRowPackage
    (P : NonRoleDirectSourceMissingPackage) :
    GeneratedClosureMetricRowPackage where
  family := P.family
  closureSource := P.closureSource
  reducedMetric := P.reducedMetric

theorem knownBoundsGate
    (P : NonRoleDirectSourceMissingPackage) :
    KnownBoundsGate :=
  P.toGeneratedClosureMetricRowPackage.knownBoundsGate

theorem knownBoundsStatements
    (P : NonRoleDirectSourceMissingPackage) :
    KnownBoundsStatements :=
  P.toGeneratedClosureMetricRowPackage.knownBoundsStatements

theorem exactBound
    (P : NonRoleDirectSourceMissingPackage) (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  P.toGeneratedClosureMetricRowPackage.exactBound k hk

theorem arbitraryBound
    (P : NonRoleDirectSourceMissingPackage) (n : Nat) :
    ArbitraryBound n :=
  P.toGeneratedClosureMetricRowPackage.arbitraryBound n

end NonRoleDirectSourceMissingPackage

def nonRoleDirectSourceMissingPackageOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    NonRoleDirectSourceMissingPackage where
  family := P.family
  closureSource := P.closureSource
  reducedMetric := P.reducedMetric

theorem nonempty_nonRoleDirectSourceMissingPackage_iff_generatedClosureMetricRowPackage :
    Nonempty NonRoleDirectSourceMissingPackage <->
      Nonempty GeneratedClosureMetricRowPackage := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro P =>
        exact Nonempty.intro P.toGeneratedClosureMetricRowPackage
  case mpr =>
    intro H
    cases H with
    | intro P =>
        exact
          Nonempty.intro
            (nonRoleDirectSourceMissingPackageOfGeneratedClosureMetricRowPackage
              P)

theorem knownBoundsGate_iff_nonRoleDirectSourceMissingPackage :
    KnownBoundsGate <-> Nonempty NonRoleDirectSourceMissingPackage :=
  Iff.trans PachTothW23RouteAudit.knownBoundsGate_iff_generatedClosureMetricRowPackage
    nonempty_nonRoleDirectSourceMissingPackage_iff_generatedClosureMetricRowPackage.symm

theorem finalConditionalGate_iff_nonRoleDirectSourceMissingPackage :
    FinalConditionalGate <-> Nonempty NonRoleDirectSourceMissingPackage :=
  Iff.trans finalConditionalGate_iff_knownBoundsGate
    knownBoundsGate_iff_nonRoleDirectSourceMissingPackage

/-! ## Conditional target theorem bridges -/

theorem exactBound_of_nonRoleDirectSourceMissingPackage
    (P : NonRoleDirectSourceMissingPackage) (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  P.exactBound k hk

theorem arbitraryBound_of_nonRoleDirectSourceMissingPackage
    (P : NonRoleDirectSourceMissingPackage) (n : Nat) :
    ArbitraryBound n :=
  P.arbitraryBound n

theorem knownBoundsStatements_of_nonRoleDirectSourceMissingPackage
    (P : NonRoleDirectSourceMissingPackage) :
    KnownBoundsStatements :=
  P.knownBoundsStatements

theorem knownBoundsGate_of_nonempty_nonRoleDirectSourceMissingPackage
    (H : Nonempty NonRoleDirectSourceMissingPackage) :
    KnownBoundsGate := by
  cases H with
  | intro P =>
      exact P.knownBoundsGate

abbrev ExactBaseFullMetricDirectSourcePackage : Type :=
  ExactBaseFullMetricConcreteW23.ExactBaseFullMetricConcreteCoreFields

abbrev ConnectorFullMetricDirectSourcePackage : Type :=
  ExactBaseFullMetricConcreteW23.ConnectorFullMetricConcreteCoreFields

theorem exactTarget_of_exactBaseFullMetricDirectSourcePackage
    (P : ExactBaseFullMetricDirectSourcePackage) :
    ExactBaseFullMetricSourceInhabitationW22.ExactTarget :=
  P.targetUpperConstructionFiveSixteen

theorem arbitraryTarget_of_exactBaseFullMetricDirectSourcePackage
    (P : ExactBaseFullMetricDirectSourcePackage) :
    ExactBaseFullMetricSourceInhabitationW22.ArbitraryTarget :=
  P.targetUpperConstructionFiveSixteenArbitrary

theorem exactTarget_of_connectorFullMetricDirectSourcePackage
    (P : ConnectorFullMetricDirectSourcePackage) :
    ExactBaseFullMetricSourceInhabitationW22.ExactTarget :=
  P.targetUpperConstructionFiveSixteen

theorem arbitraryTarget_of_connectorFullMetricDirectSourcePackage
    (P : ConnectorFullMetricDirectSourcePackage) :
    ExactBaseFullMetricSourceInhabitationW22.ArbitraryTarget :=
  P.targetUpperConstructionFiveSixteenArbitrary

abbrev RemainingSeparationPackage
    (F : RemainingSeparationConcreteW23.RoleHingedPeriodSearchFamily) :
    Type :=
  RemainingSeparationConcreteW23.ExactRemainingSeparationPackage F

theorem remainingSeparationField_iff_remainingSeparationPackage
    (F : RemainingSeparationConcreteW23.RoleHingedPeriodSearchFamily) :
    RemainingSeparationConcreteW23.RemainingSeparationField F <->
      Nonempty (RemainingSeparationPackage F) :=
  RemainingSeparationConcreteW23.remainingSeparationField_iff_nonempty_exactPackage
    F

theorem remainingSeparationField_closed
    (F : RemainingSeparationConcreteW23.RoleHingedPeriodSearchFamily) :
    RemainingSeparationConcreteW23.RemainingSeparationField F :=
  RemainingSeparationConcreteW23.remainingSeparationField_closed F

end

end PachTothW24RouteAudit
end PachToth

namespace Verified

abbrev PachTothW24KnownBoundsGate : Prop :=
  PachToth.PachTothW24RouteAudit.KnownBoundsGate

abbrev PachTothW24ConcreteRowsEndpointGate : Prop :=
  PachToth.PachTothW24RouteAudit.ConcreteRowsEndpointGate

abbrev PachTothW24CandidateRowsEndpointGate : Prop :=
  PachToth.PachTothW24RouteAudit.CandidateRowsEndpointGate

abbrev PachTothW24NonRoleDirectSourceMissingPackage : Type :=
  PachToth.PachTothW24RouteAudit.NonRoleDirectSourceMissingPackage

theorem pachtoth_w24_knownBoundsGate_iff_nonRoleDirectSourceMissingPackage :
    PachTothW24KnownBoundsGate <->
      Nonempty PachTothW24NonRoleDirectSourceMissingPackage :=
  PachToth.PachTothW24RouteAudit.knownBoundsGate_iff_nonRoleDirectSourceMissingPackage

theorem pachtoth_w24_exactTarget_of_concreteRowsEndpointGate
    (H : PachTothW24ConcreteRowsEndpointGate) :
    PachToth.PachTothW24RouteAudit.ExactTarget :=
  PachToth.PachTothW24RouteAudit.exactTarget_of_concreteRowsEndpointGate H

theorem pachtoth_w24_arbitraryTarget_of_concreteRowsEndpointGate
    (H : PachTothW24ConcreteRowsEndpointGate) :
    PachToth.PachTothW24RouteAudit.ArbitraryTarget :=
  PachToth.PachTothW24RouteAudit.arbitraryTarget_of_concreteRowsEndpointGate H

theorem pachtoth_w24_no_concreteValueMatrixRows :
    Not PachTothW24ConcreteRowsEndpointGate :=
  PachToth.PachTothW24RouteAudit.no_concreteValueMatrixRows

theorem pachtoth_w24_no_candidateValueMatrixRows :
    Not PachTothW24CandidateRowsEndpointGate :=
  PachToth.PachTothW24RouteAudit.no_candidateValueMatrixRows

theorem pachtoth_w24_knownBoundsGate_of_nonempty_nonRoleDirectSourceMissingPackage
    (H : Nonempty PachTothW24NonRoleDirectSourceMissingPackage) :
    PachTothW24KnownBoundsGate :=
  PachToth.PachTothW24RouteAudit.knownBoundsGate_of_nonempty_nonRoleDirectSourceMissingPackage
    H

end Verified
end ErdosProblems1066
