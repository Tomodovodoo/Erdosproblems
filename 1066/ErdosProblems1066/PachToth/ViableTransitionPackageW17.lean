import ErdosProblems1066.PachToth.PeriodBaseFixingCertificateW16
import ErdosProblems1066.PachToth.RoleHingeTransitionSearch

set_option autoImplicit false

/-!
# W17 viable transition package surface

This file records the smallest checked search surface found after the W16
base-fixing pass.  Connector-unit facts by themselves are not enough: the
all-positive period rows also need one exact-base fixing branch.  The viable
search package below keeps the role-hinge algebraic data, the derived
connector-unit data, and the exact-base fixing disjunct as separate fields.

For the present W16 certificate adapter, a second wrapper records the stronger
`RoleHingeTransitions` input together with the same base-fixing disjunct and
projects it to `PeriodBaseFixingCertificateW16`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ViableTransitionPackageW17

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole

abbrev RoleHingeTransition :=
  BaseTransitionRealization.RoleHingeTransition

abbrev RoleHingeTransitions :=
  PeriodBaseFixingCertificateW16.RoleHingeTransitions

abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations

abbrev ConnectorBranchFacts :=
  RoleHingeTransitionSearch.RoleHingeConnectorTransitionFacts

abbrev ConnectorTransitions :=
  RoleHingeTransitionSearch.SameOppositeRoleHingeConnectorTransitionFacts

abbrev PeriodRows :=
  PeriodBaseFixingCertificateW16.PeriodRows

abbrev BaseFixingAlternative :=
  PeriodBaseFixingCertificateW16.BaseFixingAlternative

abbrev SameFixesExactBase :=
  PeriodBaseFixingCertificateW16.SameFixesExactBase

abbrev OppositeFixesExactBase :=
  PeriodBaseFixingCertificateW16.OppositeFixesExactBase

/-- Forget the all-source same-block metric field from one strong
role-hinge transition and keep the viable connector-level algebraic data:
`placeNext`, `roleAngle`, role-realization equations, and connector-unit
edges. -/
def connectorBranchOfRoleHingeTransition
    (T : RoleHingeTransition) :
    ConnectorBranchFacts where
  placeNext := T.placeNext
  roleAngle := T.roleAngle
  realizes_role := T.realizes_role
  connector_unit_edges := T.connector_unit_edges

@[simp]
theorem connectorBranchOfRoleHingeTransition_placeNext
    (T : RoleHingeTransition) :
    (connectorBranchOfRoleHingeTransition T).placeNext = T.placeNext :=
  rfl

@[simp]
theorem connectorBranchOfRoleHingeTransition_roleAngle
    (T : RoleHingeTransition) :
    (connectorBranchOfRoleHingeTransition T).roleAngle = T.roleAngle :=
  rfl

/-- Forget the W16-strong same-block fields from a same/opposite transition
package and retain the connector-level role-hinge fields. -/
def connectorFactsOfRoleHingeTransitions
    (T : RoleHingeTransitions) :
    ConnectorTransitions where
  same := connectorBranchOfRoleHingeTransition T.same
  opposite := connectorBranchOfRoleHingeTransition T.opposite

@[simp]
theorem connectorFactsOfRoleHingeTransitions_same
    (T : RoleHingeTransitions) :
    (connectorFactsOfRoleHingeTransitions T).same =
      connectorBranchOfRoleHingeTransition T.same :=
  rfl

@[simp]
theorem connectorFactsOfRoleHingeTransitions_opposite
    (T : RoleHingeTransitions) :
    (connectorFactsOfRoleHingeTransitions T).opposite =
      connectorBranchOfRoleHingeTransition T.opposite :=
  rfl

@[simp]
theorem connectorFactsOfRoleHingeTransitions_same_placeNext
    (T : RoleHingeTransitions) :
    (connectorFactsOfRoleHingeTransitions T).same.placeNext =
      T.same.placeNext :=
  rfl

@[simp]
theorem connectorFactsOfRoleHingeTransitions_opposite_placeNext
    (T : RoleHingeTransitions) :
    (connectorFactsOfRoleHingeTransitions T).opposite.placeNext =
      T.opposite.placeNext :=
  rfl

abbrev ConnectorSameFixesExactBase
    (F : ConnectorTransitions) : Prop :=
  PeriodCertificateExamples.TransitionFixesBase
    F.toFigure2TransitionObligations
    BaseTransitionRealization.exactBase
    OrientationData.BlockOrientation.same

abbrev ConnectorOppositeFixesExactBase
    (F : ConnectorTransitions) : Prop :=
  PeriodCertificateExamples.TransitionFixesBase
    F.toFigure2TransitionObligations
    BaseTransitionRealization.exactBase
    OrientationData.BlockOrientation.opposite

abbrev ConnectorBaseFixingAlternative
    (F : ConnectorTransitions) : Prop :=
  ConnectorSameFixesExactBase F \/ ConnectorOppositeFixesExactBase F

theorem connectorSameFixesExactBase_iff_placeNext
    (F : ConnectorTransitions) :
    ConnectorSameFixesExactBase F <->
      F.same.placeNext BaseTransitionRealization.exactBase =
        BaseTransitionRealization.exactBase := by
  rfl

theorem connectorOppositeFixesExactBase_iff_placeNext
    (F : ConnectorTransitions) :
    ConnectorOppositeFixesExactBase F <->
      F.opposite.placeNext BaseTransitionRealization.exactBase =
        BaseTransitionRealization.exactBase := by
  rfl

/-- One all-positive algebraic row over the viable connector-level package. -/
abbrev ConnectorAlgebraicEquationRow
    (F : ConnectorTransitions)
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (k : Nat) (hk : 0 < k) (i : Fin 16) : Prop :=
  PeriodSearchInterface.AlgebraicVertexPeriodEquation
    F.toFigure2TransitionObligations
    BaseTransitionRealization.exactBase
    (PeriodCertificateExamples.finiteOrientationWordOfWord hk
      (word k hk))
    (BlockPartition.localVertexEquivFin16.symm i)

/-- Exact algebraic fields needed from a viable all-positive transition
search: same/opposite connector role data, a word family, and the sixteen
period-equation rows at every positive length. -/
structure ConnectorAllPositiveRows where
  transitions : ConnectorTransitions
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hk : 0 < k) (i : Fin 16),
      ConnectorAlgebraicEquationRow transitions word k hk i

namespace ConnectorAllPositiveRows

def orientation
    (P : ConnectorAllPositiveRows)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  (P.word k hk).toFin

@[simp]
theorem orientation_apply
    (P : ConnectorAllPositiveRows)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    P.orientation k hk i = P.word k hk i :=
  rfl

def indexedCertificate
    (P : ConnectorAllPositiveRows)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      P.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      (PeriodCertificateExamples.finiteOrientationWordOfWord hk
        (P.word k hk)) where
  equation := P.equation k hk

def closure
    (P : ConnectorAllPositiveRows)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      P.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  (P.indexedCertificate k hk).toGeneratedClosureEquation

end ConnectorAllPositiveRows

/-- Same-branch connector-level rows from the exact-base fixing field. -/
def connectorAllPositiveSameRows
    (F : ConnectorTransitions)
    (hfix : ConnectorSameFixesExactBase F) :
    ConnectorAllPositiveRows where
  transitions := F
  word := PeriodCertificateExamples.allPositiveSameWord
  equation := by
    intro k hk i
    exact
      PeriodCertificateExamples.allPositiveSameEquations
        F.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase hfix k hk i

/-- Opposite-branch connector-level rows from the exact-base fixing field. -/
def connectorAllPositiveOppositeRows
    (F : ConnectorTransitions)
    (hfix : ConnectorOppositeFixesExactBase F) :
    ConnectorAllPositiveRows where
  transitions := F
  word := PeriodCertificateExamples.allPositiveOppositeWord
  equation := by
    intro k hk i
    exact
      PeriodCertificateExamples.allPositiveOppositeEquations
        F.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase hfix k hk i

theorem exists_connectorAllPositiveRows_of_baseFixingAlternative
    (F : ConnectorTransitions)
    (H : ConnectorBaseFixingAlternative F) :
    exists P : ConnectorAllPositiveRows, P.transitions = F := by
  rcases H with hsame | hopposite
  · exact ⟨connectorAllPositiveSameRows F hsame, rfl⟩
  · exact ⟨connectorAllPositiveOppositeRows F hopposite, rfl⟩

def connectorAllPositiveRowsOfBaseFixingAlternative
    (F : ConnectorTransitions)
    (H : ConnectorBaseFixingAlternative F) :
    ConnectorAllPositiveRows :=
  Classical.choose
    (exists_connectorAllPositiveRows_of_baseFixingAlternative F H)

@[simp]
theorem connectorAllPositiveRowsOfBaseFixingAlternative_transitions
    (F : ConnectorTransitions)
    (H : ConnectorBaseFixingAlternative F) :
    (connectorAllPositiveRowsOfBaseFixingAlternative F H).transitions = F :=
  Classical.choose_spec
    (exists_connectorAllPositiveRows_of_baseFixingAlternative F H)

/-- The viable connector-level transition package: role-hinge connector facts
plus one checked exact-base fixing disjunct. -/
structure ViableConnectorTransitionPackage where
  transitions : ConnectorTransitions
  baseFixing : ConnectorBaseFixingAlternative transitions

namespace ViableConnectorTransitionPackage

def toFigure2TransitionObligations
    (P : ViableConnectorTransitionPackage) :
    TransitionObligations :=
  P.transitions.toFigure2TransitionObligations

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (P : ViableConnectorTransitionPackage) :
    P.toFigure2TransitionObligations.samePlaceNext =
      P.transitions.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (P : ViableConnectorTransitionPackage) :
    P.toFigure2TransitionObligations.oppositePlaceNext =
      P.transitions.opposite.placeNext :=
  rfl

/-- Assemble the exact all-positive algebraic rows over the viable connector
package. -/
def toConnectorAllPositiveRows
    (P : ViableConnectorTransitionPackage) :
    ConnectorAllPositiveRows :=
  connectorAllPositiveRowsOfBaseFixingAlternative
    P.transitions P.baseFixing

@[simp]
theorem toConnectorAllPositiveRows_transitions
    (P : ViableConnectorTransitionPackage) :
    P.toConnectorAllPositiveRows.transitions = P.transitions :=
  connectorAllPositiveRowsOfBaseFixingAlternative_transitions
    P.transitions P.baseFixing

end ViableConnectorTransitionPackage

/-- A W16-ready package is exactly the strong role-hinge transition input
used by `PeriodBaseFixingCertificateW16`, together with the base-fixing
disjunct.  Its connector-level projection records the viable algebraic fields
that should be searched independently. -/
structure W16ReadyRoleHingeTransitionPackage where
  transitions : RoleHingeTransitions
  baseFixing : BaseFixingAlternative transitions

namespace W16ReadyRoleHingeTransitionPackage

def connectorTransitions
    (P : W16ReadyRoleHingeTransitionPackage) :
    ConnectorTransitions :=
  connectorFactsOfRoleHingeTransitions P.transitions

theorem connectorBaseFixingAlternative
    (P : W16ReadyRoleHingeTransitionPackage) :
    ConnectorBaseFixingAlternative P.connectorTransitions := by
  rcases P.baseFixing with hsame | hopposite
  · exact Or.inl (by
      simpa [connectorTransitions, connectorFactsOfRoleHingeTransitions,
        connectorBranchOfRoleHingeTransition,
        PeriodCertificateExamples.TransitionFixesBase] using hsame)
  · exact Or.inr (by
      simpa [connectorTransitions, connectorFactsOfRoleHingeTransitions,
        connectorBranchOfRoleHingeTransition,
        PeriodCertificateExamples.TransitionFixesBase] using hopposite)

def toViableConnectorTransitionPackage
    (P : W16ReadyRoleHingeTransitionPackage) :
    ViableConnectorTransitionPackage where
  transitions := P.connectorTransitions
  baseFixing := P.connectorBaseFixingAlternative

def toPeriodBaseFixingCertificate
    (P : W16ReadyRoleHingeTransitionPackage) :
    PeriodBaseFixingCertificateW16.PeriodBaseFixingCertificate where
  transitions := P.transitions
  baseFixing := P.baseFixing

def toConcretePeriodEquationFields
    (P : W16ReadyRoleHingeTransitionPackage) :
    PeriodRows :=
  P.toPeriodBaseFixingCertificate.toConcretePeriodEquationFields

@[simp]
theorem toConcretePeriodEquationFields_transitions
    (P : W16ReadyRoleHingeTransitionPackage) :
    P.toConcretePeriodEquationFields.transitions = P.transitions :=
  P.toPeriodBaseFixingCertificate.toConcretePeriodEquationFields_transitions

theorem exists_concretePeriodEquationFields
    (P : W16ReadyRoleHingeTransitionPackage) :
    exists R : PeriodRows, R.transitions = P.transitions :=
  P.toPeriodBaseFixingCertificate.exists_concretePeriodEquationFields

def toConnectorAllPositiveRows
    (P : W16ReadyRoleHingeTransitionPackage) :
    ConnectorAllPositiveRows :=
  P.toViableConnectorTransitionPackage.toConnectorAllPositiveRows

@[simp]
theorem toConnectorAllPositiveRows_transitions
    (P : W16ReadyRoleHingeTransitionPackage) :
    P.toConnectorAllPositiveRows.transitions = P.connectorTransitions :=
  P.toViableConnectorTransitionPackage.toConnectorAllPositiveRows_transitions

end W16ReadyRoleHingeTransitionPackage

def w16ReadyPackageOfBaseFixingAlternative
    (T : RoleHingeTransitions)
    (H : BaseFixingAlternative T) :
    W16ReadyRoleHingeTransitionPackage where
  transitions := T
  baseFixing := H

def w16ReadyPackageOfSameFixesExactBase
    (T : RoleHingeTransitions)
    (hfix : SameFixesExactBase T) :
    W16ReadyRoleHingeTransitionPackage :=
  w16ReadyPackageOfBaseFixingAlternative T (Or.inl hfix)

def w16ReadyPackageOfOppositeFixesExactBase
    (T : RoleHingeTransitions)
    (hfix : OppositeFixesExactBase T) :
    W16ReadyRoleHingeTransitionPackage :=
  w16ReadyPackageOfBaseFixingAlternative T (Or.inr hfix)

end

end ViableTransitionPackageW17
end PachToth
end ErdosProblems1066
