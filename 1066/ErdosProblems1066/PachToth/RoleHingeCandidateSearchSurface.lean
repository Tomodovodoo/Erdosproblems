import ErdosProblems1066.PachToth.GeneratedPointDistanceFacts
import ErdosProblems1066.PachToth.FlexibleExactLocalTransition
import ErdosProblems1066.PachToth.RoleHingeConnectorConcrete
import ErdosProblems1066.PachToth.RoleHingeInterfaceRefinement
import ErdosProblems1066.PachToth.PeriodWordCertificates

set_option autoImplicit false

/-!
# Finite-search surface for non-rigid role-hinge candidates

This module gives finite-search output a small replacement surface for the
old impossible all-source `samePlaceNext`/`oppositePlaceNext` same-block
package.  A candidate transition is required to provide only:

* role-hinge connector realization data, which projects to the existing
  connector-unit obligations; and
* exact-local squared-distance preservation on exact-local sources, which is
  the generated-orbit same-block metric actually used downstream.

Period equations and generated metric checks are then kept as explicit finite
fields and projected to the existing generated-chain interfaces.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeCandidateSearchSurface

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole
abbrev ConnectorTransitionFacts :=
  RoleHingeTransitionSearch.RoleHingeConnectorTransitionFacts
abbrev SameOppositeConnectorTransitionFacts :=
  RoleHingeTransitionSearch.SameOppositeRoleHingeConnectorTransitionFacts
abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations

/-! ## Transition candidates -/

/-- One role-hinge branch with the weaker, generated-orbit same-block metric
obligation used by the non-rigid search route. -/
structure BranchCandidate where
  placeNext : (LocalVertex -> R2) -> LocalVertex -> R2
  roleAngle : ConnectorRole -> Real
  realizes_role :
    forall (source : LocalVertex -> R2) (u v : LocalVertex)
      (role : ConnectorRole),
      Figure2EdgeTable.nextConnectorRole u v = some role ->
        placeNext source v =
          UnitVectorGeometry.hingePoint (source u) (roleAngle role)
  preserves_exactLocal_sqDistances :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances placeNext

namespace BranchCandidate

/-- Forget the exact-local same-block field and retain the connector-level
role-hinge facts. -/
def toConnectorFacts (T : BranchCandidate) :
    ConnectorTransitionFacts :=
  RoleHingeTransitionSearch.roleHingeConnectorTransitionFacts
    T.placeNext T.roleAngle T.realizes_role

@[simp]
theorem toConnectorFacts_placeNext (T : BranchCandidate) :
    T.toConnectorFacts.placeNext = T.placeNext :=
  rfl

@[simp]
theorem toConnectorFacts_roleAngle (T : BranchCandidate) :
    T.toConnectorFacts.roleAngle = T.roleAngle :=
  rfl

@[simp]
theorem toConnectorFacts_realizes_role (T : BranchCandidate) :
    T.toConnectorFacts.realizes_role = T.realizes_role :=
  rfl

/-- Connector-unit facts are derived from the finite role table and the hinge
unit lemma. -/
theorem connector_unit_edges (T : BranchCandidate) :
    HingedTransitionInterface.ConnectorUnitEdges T.placeNext :=
  T.toConnectorFacts.connector_unit_edges

/-- Projection to the flexible exact-local transition interface. -/
def toFlexibleBranch (T : BranchCandidate) :
    FlexibleExactLocalTransition.Branch where
  connector :=
    { placeNext := T.placeNext
      roleAngle := T.roleAngle
      realizes_role := T.realizes_role }
  exactLocal :=
    { preserves_exact_local_sq_distances :=
        T.preserves_exactLocal_sqDistances }

@[simp]
theorem toFlexibleBranch_placeNext (T : BranchCandidate) :
    T.toFlexibleBranch.placeNext = T.placeNext :=
  rfl

/-- Projection to the orbit-level transition interface. -/
def toOrbitTransitionFacts (T : BranchCandidate) :
    RoleHingeInterfaceRefinement.RoleHingeOrbitTransitionFacts where
  placeNext := T.placeNext
  roleAngle := T.roleAngle
  realizes_role := T.realizes_role

@[simp]
theorem toOrbitTransitionFacts_placeNext (T : BranchCandidate) :
    T.toOrbitTransitionFacts.placeNext = T.placeNext :=
  rfl

end BranchCandidate

/-- Same/opposite role-hinge transition candidates with connector facts and
exact-local same-block propagation, but without arbitrary-source same-block
preservation. -/
structure SameOppositeCandidate where
  same : BranchCandidate
  opposite : BranchCandidate

namespace SameOppositeCandidate

/-- Connector-only same/opposite transition facts. -/
def toConnectorFacts (T : SameOppositeCandidate) :
    SameOppositeConnectorTransitionFacts :=
  RoleHingeTransitionSearch.sameOppositeRoleHingeConnectorTransitionFacts
    T.same.toConnectorFacts T.opposite.toConnectorFacts

@[simp]
theorem toConnectorFacts_same (T : SameOppositeCandidate) :
    T.toConnectorFacts.same = T.same.toConnectorFacts :=
  rfl

@[simp]
theorem toConnectorFacts_opposite (T : SameOppositeCandidate) :
    T.toConnectorFacts.opposite = T.opposite.toConnectorFacts :=
  rfl

/-- Figure 2 transition obligations projected from connector facts. -/
def toFigure2TransitionObligations
    (T : SameOppositeCandidate) : TransitionObligations :=
  T.toConnectorFacts.toFigure2TransitionObligations

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (T : SameOppositeCandidate) :
    T.toFigure2TransitionObligations.samePlaceNext =
      T.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (T : SameOppositeCandidate) :
    T.toFigure2TransitionObligations.oppositePlaceNext =
      T.opposite.placeNext :=
  rfl

/-- Projection to the connector-only role-hinge refinement interface. -/
def toOrbitTransitionFacts (T : SameOppositeCandidate) :
    RoleHingeInterfaceRefinement.SameOppositeRoleHingeOrbitTransitionFacts where
  same := T.same.toOrbitTransitionFacts
  opposite := T.opposite.toOrbitTransitionFacts

/-- Projection to the flexible exact-local same/opposite interface. -/
def toFlexibleSameOpposite (T : SameOppositeCandidate) :
    FlexibleExactLocalTransition.SameOpposite where
  same := T.same.toFlexibleBranch
  opposite := T.opposite.toFlexibleBranch

@[simp]
theorem toFlexibleSameOpposite_toFigure2TransitionObligations
    (T : SameOppositeCandidate) :
    T.toFlexibleSameOpposite.toFigure2TransitionObligations =
      T.toFigure2TransitionObligations :=
  rfl

@[simp]
theorem toOrbitTransitionFacts_toFigure2TransitionObligations
    (T : SameOppositeCandidate) :
    T.toOrbitTransitionFacts.toFigure2TransitionObligations =
      T.toFigure2TransitionObligations :=
  rfl

/-- Same-branch connector obligations projected from the candidate. -/
theorem same_connector_unit_edges (T : SameOppositeCandidate) :
    HingedTransitionInterface.ConnectorUnitEdges T.same.placeNext :=
  T.same.connector_unit_edges

/-- Opposite-branch connector obligations projected from the candidate. -/
theorem opposite_connector_unit_edges (T : SameOppositeCandidate) :
    HingedTransitionInterface.ConnectorUnitEdges T.opposite.placeNext :=
  T.opposite.connector_unit_edges

/-- Branchwise exact-local preservation gives the generated-transition
same-block metric invariant used along generated orbits. -/
theorem generatedTransitionsPreserveExactLocalSqDistances
    (T : SameOppositeCandidate) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      T.toFigure2TransitionObligations := by
  exact
    RoleHingeSameBlockAlgebra.generatedTransitionsPreserveExactLocalSqDistances_of_branches
      T.toFigure2TransitionObligations
      T.same.preserves_exactLocal_sqDistances
      T.opposite.preserves_exactLocal_sqDistances

/-- Exact-base generated orbits inherit the exact-local same-block table. -/
def orbitSqDistances
    (T : SameOppositeCandidate)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation := by
  simpa [RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances]
    using
      RoleHingeSameBlockAlgebra.generatedOrbit_exactBase_matchesExactLocalSqDistances
        T.toFigure2TransitionObligations hk orientation
        T.generatedTransitionsPreserveExactLocalSqDistances

/-- The orbit exact-local invariant supplies the same-block isometry required
by generated closed chains. -/
def generatedSameBlockIsometry
    (T : SameOppositeCandidate)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation :=
  RoleHingeInterfaceRefinement.generatedSameBlockIsometry_of_orbitSqDistances
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase orientation
    (T.orbitSqDistances hk orientation)

/-- Full generated metric hypotheses from generated separation plus the
candidate's exact-local transition invariant. -/
def generatedMetricHypotheses
    (T : SameOppositeCandidate)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation :=
  RoleHingeInterfaceRefinement.generatedMetricHypotheses_of_orbitSqDistances
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase orientation separated
    (T.orbitSqDistances hk orientation)

end SameOppositeCandidate

/-! ## Concrete connector projection -/

/-- The existing concrete same/opposite maps are usable at the connector-only
level.  A non-rigid candidate must still provide the separate exact-local
same-block field above. -/
def concreteConnectorFacts : SameOppositeConnectorTransitionFacts :=
  RoleHingeConnectorConcrete.sameOppositeTransitionFacts

@[simp]
theorem concreteConnectorFacts_same :
    concreteConnectorFacts.same =
      RoleHingeConnectorConcrete.sameTransitionFacts :=
  rfl

@[simp]
theorem concreteConnectorFacts_opposite :
    concreteConnectorFacts.opposite =
      RoleHingeConnectorConcrete.oppositeTransitionFacts :=
  rfl

/-! ## Period-search data -/

/-- Exact algebraic period equations for a finite orientation word over a
candidate's connector obligations and the checked exact base block. -/
abbrev ExactPeriodEquations
    (T : SameOppositeCandidate)
    {k : Nat} (hk : 0 < k)
    (W : OrientationWord.Word k) : Prop :=
  PeriodWordCertificates.AlgebraicEquationsForWord
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase W

/-- All-positive finite period-search data for a non-rigid role-hinge
candidate. -/
structure PeriodSearchData (T : SameOppositeCandidate) where
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hk : 0 < k),
      ExactPeriodEquations T hk (word k hk)

namespace PeriodSearchData

/-- Raw generated-chain orientation for one period length. -/
def orientation
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  (P.word k hk).toFin

@[simp]
theorem orientation_apply
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    P.orientation k hk i = P.word k hk i :=
  rfl

/-- Finite word projected to the period-search interface. -/
def finiteWord
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.FiniteOrientationWord :=
  PeriodWordCertificates.finiteOrientationWordOfWord hk (P.word k hk)

@[simp]
theorem finiteWord_length
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) :
    (P.finiteWord k hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    (P.finiteWord k hk).letter i = P.word k hk i :=
  rfl

/-- Indexed algebraic certificate projected from the finite equation fields. -/
def indexedCertificate
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      (P.finiteWord k hk) :=
  PeriodWordCertificates.indexedAlgebraicCertificateOfWord
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (P.word k hk)
    (P.equation k hk)

/-- Generated closure equation projected from the finite period equations. -/
def closure
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  PeriodWordCertificates.generatedClosureEquationOfWord
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (P.word k hk)
    (P.equation k hk)

/-- Generated final-block period equation projected from the finite period
equations. -/
def periodEquation
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  PeriodWordCertificates.generatedPeriodEquationOfWord
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (P.word k hk)
    (P.equation k hk)

/-- Generated-period hypothesis projected from the finite period equations. -/
def generatedPeriod
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  PeriodWordCertificates.generatedPeriodOfWord
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (P.word k hk)
    (P.equation k hk)

/-- Generated-chain family projected from a candidate and its period data. -/
def toGeneratedChainFamily
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _k _hk => T.toFigure2TransitionObligations
  base := fun _k _hk => BaseTransitionRealization.exactBase
  orientation := P.orientation

@[simp]
theorem toGeneratedChainFamily_O
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) :
    (P.toGeneratedChainFamily).O k hk =
      T.toFigure2TransitionObligations :=
  rfl

@[simp]
theorem toGeneratedChainFamily_base
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) :
    (P.toGeneratedChainFamily).base k hk =
      BaseTransitionRealization.exactBase :=
  rfl

@[simp]
theorem toGeneratedChainFamily_orientation
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) :
    (P.toGeneratedChainFamily).orientation k hk =
      P.orientation k hk :=
  rfl

/-- Period hypotheses for the generated-chain family. -/
def periods
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T) :
    P.toGeneratedChainFamily.Periods := by
  intro k hk
  exact P.generatedPeriod k hk

end PeriodSearchData

/-! ## Generated metric obligations -/

/-- Coordinate square-distance polynomial for one generated pair in the
candidate surface. -/
def generatedPointSqPolynomial
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) : Real :=
  GeneratedPointDistanceFacts.generatedPointSqPolynomial
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase
    (P.orientation k hk) i u j v

/-- Cross-block lower-bound data for generated metric obligations. -/
structure CrossBlockMetricData
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T) where
  lower :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
        (lower k hk)
  lower_bound :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase
        (P.orientation k hk)
        (lower k hk)

namespace CrossBlockMetricData

/-- Generated global separation projected from finite cross-block
lower-bound fields and candidate same-block metric data. -/
def separated
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    (M : CrossBlockMetricData P)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase
    (P.orientation k hk)
    (T.generatedSameBlockIsometry hk (P.orientation k hk))
    (M.lower k hk)
    (M.lower_ge_one k hk)
    (M.lower_bound k hk)

/-- Full generated metric hypotheses projected from cross-block finite data. -/
def toMetricHypotheses
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    (M : CrossBlockMetricData P)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  T.generatedMetricHypotheses hk (P.orientation k hk)
    (M.separated k hk)

/-- Family-level metric hypotheses projected from finite cross-block data. -/
def toFamilyMetricHypotheses
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    (M : CrossBlockMetricData P) :
    GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses
      P.toGeneratedChainFamily where
  metric := fun k hk => M.toMetricHypotheses k hk

/-- Exact target for every positive multiple, conditional on the finite
period and generated metric data in this surface. -/
theorem targetUpperConstructionFiveSixteen
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    (M : CrossBlockMetricData P) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteen_of_family
      P.toGeneratedChainFamily P.periods M.toFamilyMetricHypotheses

end CrossBlockMetricData

end

end RoleHingeCandidateSearchSurface
end PachToth
end ErdosProblems1066
