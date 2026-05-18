import ErdosProblems1066.PachToth.ViableTransitionPackageW17
import ErdosProblems1066.PachToth.PeriodBaseFixingSameW16

set_option autoImplicit false

/-!
# W18 period base-fixing producer

This file is the W18 ownership surface for the W16 period base-fixing
certificate.  The strong W17 package already contains exactly the fields
needed by `PeriodBaseFixingCertificateW16.PeriodBaseFixingCertificate`.

The smaller connector-level W17 package is deliberately weaker: it records
connector role data and connector exact-base fixing, but not a lift to the
strong `RoleHingeTransitions` interface used by W16.  The reduction below
states the precise extra data needed to produce a W16 certificate from that
connector package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodBaseFixingProducerW18

open FiniteGraph

noncomputable section

abbrev Certificate :=
  PeriodBaseFixingCertificateW16.PeriodBaseFixingCertificate

abbrev RoleHingeTransitions :=
  ViableTransitionPackageW17.RoleHingeTransitions

abbrev BaseFixingAlternative :=
  ViableTransitionPackageW17.BaseFixingAlternative

abbrev PeriodRows :=
  ViableTransitionPackageW17.PeriodRows

abbrev ConnectorTransitions :=
  ViableTransitionPackageW17.ConnectorTransitions

abbrev ViableConnectorTransitionPackage :=
  ViableTransitionPackageW17.ViableConnectorTransitionPackage

abbrev W16ReadyRoleHingeTransitionPackage :=
  ViableTransitionPackageW17.W16ReadyRoleHingeTransitionPackage

abbrev connectorFactsOfRoleHingeTransitions :=
  ViableTransitionPackageW17.connectorFactsOfRoleHingeTransitions

/-- The strong W17 package is already W16-ready, so producing the W16
certificate is just the W17 projection. -/
def certificateOfW17ReadyPackage
    (P : W16ReadyRoleHingeTransitionPackage) :
    Certificate :=
  P.toPeriodBaseFixingCertificate

@[simp]
theorem certificateOfW17ReadyPackage_transitions
    (P : W16ReadyRoleHingeTransitionPackage) :
    (certificateOfW17ReadyPackage P).transitions = P.transitions :=
  rfl

@[simp]
theorem certificateOfW17ReadyPackage_baseFixing
    (P : W16ReadyRoleHingeTransitionPackage) :
    (certificateOfW17ReadyPackage P).baseFixing = P.baseFixing :=
  rfl

/-- A W16 certificate can be regarded as the corresponding strong W17
package. -/
def w17ReadyPackageOfCertificate
    (C : Certificate) :
    W16ReadyRoleHingeTransitionPackage where
  transitions := C.transitions
  baseFixing := C.baseFixing

@[simp]
theorem certificateOf_w17ReadyPackageOfCertificate
    (C : Certificate) :
    certificateOfW17ReadyPackage (w17ReadyPackageOfCertificate C) = C := by
  cases C
  rfl

@[simp]
theorem w17ReadyPackageOf_certificateOfW17ReadyPackage
    (P : W16ReadyRoleHingeTransitionPackage) :
    w17ReadyPackageOfCertificate (certificateOfW17ReadyPackage P) = P := by
  cases P
  rfl

/-- Producing a W16 certificate is equivalent to producing the strong W17
package. -/
theorem nonempty_certificate_iff_w17ReadyPackage :
    Nonempty Certificate <-> Nonempty W16ReadyRoleHingeTransitionPackage := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro C =>
            exact Nonempty.intro (w17ReadyPackageOfCertificate C))
      (fun h => by
        cases h with
        | intro P =>
            exact Nonempty.intro (certificateOfW17ReadyPackage P))

/-- For fixed strong transitions, the W16 certificate requires exactly the
W15 base-fixing alternative. -/
theorem exists_certificate_with_transitions_iff_baseFixingAlternative
    (T : RoleHingeTransitions) :
    (exists C : Certificate, C.transitions = T) <->
      BaseFixingAlternative T := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro C hC =>
            simpa [hC] using C.baseFixing)
      (fun hfix =>
        Exists.intro
          ({ transitions := T
             baseFixing := hfix } : Certificate)
          rfl)

/-- Exact missing data for upgrading a connector-level viable package to the
W16 certificate surface: a strong role-hinge transition lift with the same
connector projection, plus the strong W15 base-fixing alternative for that
lift. -/
structure ConnectorLiftData
    (P : ViableConnectorTransitionPackage) where
  transitions : RoleHingeTransitions
  connector_eq :
    connectorFactsOfRoleHingeTransitions transitions = P.transitions
  baseFixing : BaseFixingAlternative transitions

namespace ConnectorLiftData

def toW17ReadyPackage
    {P : ViableConnectorTransitionPackage}
    (D : ConnectorLiftData P) :
    W16ReadyRoleHingeTransitionPackage where
  transitions := D.transitions
  baseFixing := D.baseFixing

def toCertificate
    {P : ViableConnectorTransitionPackage}
    (D : ConnectorLiftData P) :
    Certificate :=
  certificateOfW17ReadyPackage D.toW17ReadyPackage

@[simp]
theorem toCertificate_transitions
    {P : ViableConnectorTransitionPackage}
    (D : ConnectorLiftData P) :
    D.toCertificate.transitions = D.transitions :=
  rfl

theorem toCertificate_connector_eq
    {P : ViableConnectorTransitionPackage}
    (D : ConnectorLiftData P) :
    connectorFactsOfRoleHingeTransitions D.toCertificate.transitions =
      P.transitions :=
  D.connector_eq

def toPeriodRows
    {P : ViableConnectorTransitionPackage}
    (D : ConnectorLiftData P) :
    PeriodRows :=
  D.toCertificate.toConcretePeriodEquationFields

@[simp]
theorem toPeriodRows_transitions
    {P : ViableConnectorTransitionPackage}
    (D : ConnectorLiftData P) :
    D.toPeriodRows.transitions = D.transitions :=
  D.toCertificate.toConcretePeriodEquationFields_transitions

end ConnectorLiftData

/-- Prop-valued spelling of the exact connector-to-W16 lift requirement. -/
abbrev StrongConnectorLift
    (P : ViableConnectorTransitionPackage) : Prop :=
  exists T : RoleHingeTransitions,
    connectorFactsOfRoleHingeTransitions T = P.transitions /\
      BaseFixingAlternative T

theorem nonempty_connectorLiftData_iff_strongConnectorLift
    (P : ViableConnectorTransitionPackage) :
    Nonempty (ConnectorLiftData P) <-> StrongConnectorLift P := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro D =>
            exact Exists.intro D.transitions
              (And.intro D.connector_eq D.baseFixing))
      (fun h => by
        cases h with
        | intro T hT =>
            exact Nonempty.intro
              ({ transitions := T
                 connector_eq := hT.1
                 baseFixing := hT.2 } : ConnectorLiftData P))

/-- Sharp reduction for the connector-level W17 package: producing a W16
certificate whose connector projection is the package transition data is
equivalent to the strong lift/base-fixing data above. -/
theorem exists_certificate_projecting_iff_strongConnectorLift
    (P : ViableConnectorTransitionPackage) :
    (exists C : Certificate,
        connectorFactsOfRoleHingeTransitions C.transitions =
          P.transitions) <->
      StrongConnectorLift P := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro C hC =>
            exact Exists.intro C.transitions (And.intro hC C.baseFixing))
      (fun h => by
        cases h with
        | intro T hT =>
            exact Exists.intro
              ({ transitions := T
                 baseFixing := hT.2 } : Certificate)
              hT.1)

/-- The current strong role-hinge transition interface is inconsistent, so
there is no actual W16 base-fixing certificate in the present development. -/
theorem not_nonempty_roleHingeTransitions :
    Not (Nonempty RoleHingeTransitions) :=
  PeriodBaseFixingSameW16.not_nonempty_roleHingeTransitions

theorem not_nonempty_certificate :
    Not (Nonempty Certificate) := by
  intro h
  cases h with
  | intro C =>
      exact not_nonempty_roleHingeTransitions (Nonempty.intro C.transitions)

theorem not_nonempty_w17ReadyRoleHingeTransitionPackage :
    Not (Nonempty W16ReadyRoleHingeTransitionPackage) := by
  intro h
  cases h with
  | intro P =>
      exact not_nonempty_roleHingeTransitions
        (Nonempty.intro P.transitions)

theorem not_strongConnectorLift
    (P : ViableConnectorTransitionPackage) :
    Not (StrongConnectorLift P) := by
  intro h
  cases h with
  | intro T _hT =>
      exact not_nonempty_roleHingeTransitions (Nonempty.intro T)

theorem not_exists_certificate_projecting
    (P : ViableConnectorTransitionPackage) :
    Not
      (exists C : Certificate,
        connectorFactsOfRoleHingeTransitions C.transitions =
          P.transitions) := by
  intro h
  exact not_nonempty_certificate
    (Nonempty.intro (Classical.choose h))

end

end PeriodBaseFixingProducerW18
end PachToth
end ErdosProblems1066
