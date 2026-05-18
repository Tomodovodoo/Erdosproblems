import ErdosProblems1066.PachToth.PachTothW27FinalAssembly
import ErdosProblems1066.PachToth.PachTothW27RouteAudit
import ErdosProblems1066.PachToth.AlternativeNonRoleSourceW28
import ErdosProblems1066.PachToth.ExactAndArbitrarySourceAssemblyW28
import ErdosProblems1066.PachToth.FiniteRowsNoGoAuditW28
import ErdosProblems1066.PachToth.GeneratedClosureMetricSourceW28
import ErdosProblems1066.PachToth.LargeTailExactSourceW28
import ErdosProblems1066.PachToth.PositiveChainConcreteSourceW28
import ErdosProblems1066.PachToth.RemainderSplitExactSourceW28
import ErdosProblems1066.PachToth.SquaredOrbitClosureSourceW28

set_option autoImplicit false

/-!
# W28 final Pach-Toth assembly

This internal assembly keeps the Pach-Toth endpoints behind concrete source
gates.  The lower-table branch is already blocked by the period-search
contradiction; the remaining concrete branch is the closed-orbit/minimal-fields
route, with the peer W28 source modules root-imported as the current handoff
surface.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW28FinalAssembly

noncomputable section

/-! ## Endpoint vocabulary -/

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactAndArbitraryTargets : Prop :=
  ExactTarget /\ ArbitraryTarget

/-! ## Honest concrete source gates -/

abbrev ConcreteLowerTableGate : Prop :=
  PachTothW27RouteAudit.ConcreteLowerTableGate

abbrev ConcreteReducedMetricCertificateGate : Prop :=
  PachTothW27RouteAudit.ConcreteReducedMetricCertificateGate

abbrev DirectFullMetricSourceGate : Prop :=
  PachTothW27RouteAudit.DirectFullMetricSourceGate

abbrev ConcreteClosedOrbitFamilyGate : Prop :=
  PachTothW27RouteAudit.ConcreteClosedOrbitFamilyGate

abbrev MinimalFieldsWithOrbitClosureGate : Prop :=
  PachTothW27RouteAudit.MinimalFieldsWithOrbitClosureGate

abbrev LowerTableBranchGate : Prop :=
  ConcreteLowerTableGate \/
    ConcreteReducedMetricCertificateGate \/
      DirectFullMetricSourceGate

abbrev ClosedOrbitBranchGate : Prop :=
  ConcreteClosedOrbitFamilyGate \/
    MinimalFieldsWithOrbitClosureGate

abbrev HonestConcreteSourceGate : Prop :=
  LowerTableBranchGate \/ ClosedOrbitBranchGate

/-! ## Conditional endpoint closures -/

theorem exactAndArbitraryTargets_of_concreteLowerTableGate
    (H : ConcreteLowerTableGate) :
    ExactAndArbitraryTargets :=
  PachTothW27RouteAudit.exactAndArbitraryTargets_of_concreteLowerTableGate
    H

theorem exactAndArbitraryTargets_of_concreteReducedMetricCertificateGate
    (H : ConcreteReducedMetricCertificateGate) :
    ExactAndArbitraryTargets :=
  PachTothW27RouteAudit.exactAndArbitraryTargets_of_concreteReducedMetricCertificateGate
    H

theorem exactAndArbitraryTargets_of_directFullMetricSourceGate
    (H : DirectFullMetricSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_concreteLowerTableGate
    (PachTothW27RouteAudit.directFullMetricSourceGate_iff_concreteLowerTableGate.mp
      H)

theorem exactAndArbitraryTargets_of_lowerTableBranchGate
    (H : LowerTableBranchGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | inl hLower =>
      exact exactAndArbitraryTargets_of_concreteLowerTableGate hLower
  | inr hRest =>
      cases hRest with
      | inl hReduced =>
          exact exactAndArbitraryTargets_of_concreteReducedMetricCertificateGate hReduced
      | inr hDirect =>
          exact exactAndArbitraryTargets_of_directFullMetricSourceGate hDirect

theorem exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    ExactAndArbitraryTargets :=
  PachTothW27RouteAudit.exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate
    H

theorem exactAndArbitraryTargets_of_minimalFieldsWithOrbitClosureGate
    (H : MinimalFieldsWithOrbitClosureGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate
    (PachTothW27RouteAudit.concreteClosedOrbitFamilyGate_iff_minimalFieldsWithOrbitClosureGate.mpr
      H)

theorem exactAndArbitraryTargets_of_closedOrbitBranchGate
    (H : ClosedOrbitBranchGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | inl hClosed =>
      exact exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate hClosed
  | inr hMinimal =>
      exact exactAndArbitraryTargets_of_minimalFieldsWithOrbitClosureGate hMinimal

theorem exactAndArbitraryTargets_of_honestConcreteSourceGate
    (H : HonestConcreteSourceGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | inl hLower =>
      exact exactAndArbitraryTargets_of_lowerTableBranchGate hLower
  | inr hClosed =>
      exact exactAndArbitraryTargets_of_closedOrbitBranchGate hClosed

/-! ## Blockers that remain visible at the W28 boundary -/

theorem not_concreteLowerTableGate :
    Not ConcreteLowerTableGate :=
  PachTothW27FinalAssembly.not_nonempty_concreteLowerTables

theorem not_concreteReducedMetricCertificateGate :
    Not ConcreteReducedMetricCertificateGate :=
  PachTothW27FinalAssembly.not_nonempty_concreteReducedMetricCertificate

theorem not_directFullMetricSourceGate :
    Not DirectFullMetricSourceGate := by
  intro H
  exact not_concreteLowerTableGate
    (PachTothW27RouteAudit.directFullMetricSourceGate_iff_concreteLowerTableGate.mp
      H)

theorem not_lowerTableBranchGate :
    Not LowerTableBranchGate := by
  intro H
  cases H with
  | inl hLower =>
      exact not_concreteLowerTableGate hLower
  | inr hRest =>
      cases hRest with
      | inl hReduced =>
          exact not_concreteReducedMetricCertificateGate hReduced
      | inr hDirect =>
          exact not_directFullMetricSourceGate hDirect

theorem honestConcreteSourceGate_iff_closedOrbitBranchGate :
    HonestConcreteSourceGate <-> ClosedOrbitBranchGate := by
  constructor
  case mp =>
    intro H
    cases H with
    | inl hLower =>
        exact False.elim (not_lowerTableBranchGate hLower)
    | inr hClosed =>
        exact hClosed
  case mpr =>
    intro H
    exact Or.inr H

/-- W28 final status: the checked lower-table branch is blocked, and every
remaining endpoint closure is still conditional on a closed-orbit source gate. -/
theorem finalStatus :
    Not LowerTableBranchGate /\
      (HonestConcreteSourceGate <-> ClosedOrbitBranchGate) /\
        (HonestConcreteSourceGate -> ExactAndArbitraryTargets) :=
  And.intro not_lowerTableBranchGate
    (And.intro honestConcreteSourceGate_iff_closedOrbitBranchGate
      exactAndArbitraryTargets_of_honestConcreteSourceGate)

theorem exactAndArbitraryTargets_of_remainingClosedOrbitSource
    (H : ClosedOrbitBranchGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_honestConcreteSourceGate
    (honestConcreteSourceGate_iff_closedOrbitBranchGate.mpr H)

end

end PachTothW28FinalAssembly
end PachToth

namespace Verified

abbrev PachTothW28LowerTableBranchGate : Prop :=
  PachToth.PachTothW28FinalAssembly.LowerTableBranchGate

abbrev PachTothW28ClosedOrbitBranchGate : Prop :=
  PachToth.PachTothW28FinalAssembly.ClosedOrbitBranchGate

abbrev PachTothW28HonestConcreteSourceGate : Prop :=
  PachToth.PachTothW28FinalAssembly.HonestConcreteSourceGate

theorem pachtoth_w28_not_lowerTableBranchGate :
    Not PachTothW28LowerTableBranchGate :=
  PachToth.PachTothW28FinalAssembly.not_lowerTableBranchGate

theorem pachtoth_w28_honestConcreteSourceGate_iff_closedOrbitBranchGate :
    PachTothW28HonestConcreteSourceGate <->
      PachTothW28ClosedOrbitBranchGate :=
  PachToth.PachTothW28FinalAssembly.honestConcreteSourceGate_iff_closedOrbitBranchGate

theorem pachtoth_w28_exactAndArbitraryTargets_of_honestConcreteSourceGate
    (H : PachTothW28HonestConcreteSourceGate) :
    PachToth.PachTothW28FinalAssembly.ExactAndArbitraryTargets :=
  PachToth.PachTothW28FinalAssembly.exactAndArbitraryTargets_of_honestConcreteSourceGate
    H

theorem pachtoth_w28_finalStatus :
    Not PachTothW28LowerTableBranchGate /\
      (PachTothW28HonestConcreteSourceGate <->
        PachTothW28ClosedOrbitBranchGate) /\
        (PachTothW28HonestConcreteSourceGate ->
          PachToth.PachTothW28FinalAssembly.ExactAndArbitraryTargets) :=
  PachToth.PachTothW28FinalAssembly.finalStatus

end Verified
end ErdosProblems1066
