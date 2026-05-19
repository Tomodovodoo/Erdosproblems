import ErdosProblems1066.PachToth.GeneratedPointDistanceFacts
import ErdosProblems1066.PachToth.FlexibleExactLocalTransition
import ErdosProblems1066.PachToth.RoleHingeConnectorConcrete
import ErdosProblems1066.PachToth.RoleHingeInterfaceRefinement
import ErdosProblems1066.PachToth.PeriodWordCertificates
import ErdosProblems1066.PachToth.GeneratedClosedChainEventualReduction

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

abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

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

/-- The generated point addressed by the finite local-vertex index used by
metric-table search certificates. -/
def indexedGeneratedPoint
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex) : R2 :=
  GeneratedClosedChain.generatedPoint
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase
    (P.orientation k hk) i
    (CrossBlockLowerBoundsInterface.localVertexOfIndex u)

/-- A finite-index cross-block metric table for one period length in the
flexible candidate surface. -/
structure IndexedCrossBlockMetricTable
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) where
  lower : Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  lower_ge_one :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j -> 1 <= lower i u j v
  lower_bound :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j ->
          lower i u j v <=
            _root_.eucDist
              (indexedGeneratedPoint P hk i u)
              (indexedGeneratedPoint P hk j v)

namespace IndexedCrossBlockMetricTable

/-- Interpret a finite-index metric table as a local-vertex lower table. -/
def toLocalLower
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    {k : Nat} {hk : 0 < k}
    (M : IndexedCrossBlockMetricTable P k hk) :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real :=
  fun i u j v =>
    M.lower i (CrossBlockLowerBoundsInterface.localVertexIndex u) j
      (CrossBlockLowerBoundsInterface.localVertexIndex v)

/-- The finite-index `>= 1` row projects to the local-vertex cross-block
predicate used by generated separation. -/
theorem toLocalLower_ge_one
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    {k : Nat} {hk : 0 < k}
    (M : IndexedCrossBlockMetricTable P k hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      M.toLocalLower := by
  intro i u j v hij
  exact
    M.lower_ge_one i
      (CrossBlockLowerBoundsInterface.localVertexIndex u) j
      (CrossBlockLowerBoundsInterface.localVertexIndex v) hij

/-- The finite-index distance row projects to the local-vertex cross-block
metric predicate used by generated separation. -/
theorem toLocalLower_bound
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    {k : Nat} {hk : 0 < k}
    (M : IndexedCrossBlockMetricTable P k hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk)
      M.toLocalLower := by
  intro i u j v hij
  simpa [toLocalLower, indexedGeneratedPoint] using
    M.lower_bound i
      (CrossBlockLowerBoundsInterface.localVertexIndex u) j
      (CrossBlockLowerBoundsInterface.localVertexIndex v) hij

end IndexedCrossBlockMetricTable

/-- A family of finite-index metric tables, one for every positive period
length in a flexible candidate's period-search data. -/
structure IndexedCrossBlockMetricTableFamily
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T) where
  table :
    forall (k : Nat) (hk : 0 < k),
      IndexedCrossBlockMetricTable P k hk

namespace IndexedCrossBlockMetricTableFamily

def lower
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    (M : IndexedCrossBlockMetricTableFamily P)
    (k : Nat) (hk : 0 < k) :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real :=
  (M.table k hk).toLocalLower

theorem lower_ge_one
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    (M : IndexedCrossBlockMetricTableFamily P)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      (M.lower k hk) :=
  (M.table k hk).toLocalLower_ge_one

theorem lower_bound
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    (M : IndexedCrossBlockMetricTableFamily P)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk)
      (M.lower k hk) :=
  (M.table k hk).toLocalLower_bound

end IndexedCrossBlockMetricTableFamily

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

/-- Build the flexible cross-block metric data from finite-index metric
tables. -/
def ofIndexedTables
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    (M : IndexedCrossBlockMetricTableFamily P) :
    CrossBlockMetricData P where
  lower := M.lower
  lower_ge_one := M.lower_ge_one
  lower_bound := M.lower_bound

/-- Every finite-index metric table family inhabits the flexible cross-block
metric-data surface. -/
theorem nonempty_of_indexedTables
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T} :
    Nonempty (IndexedCrossBlockMetricTableFamily P) ->
      Nonempty (CrossBlockMetricData P) := by
  intro h
  cases h with
  | intro M =>
      exact Nonempty.intro (ofIndexedTables M)

/-- Re-index existing cross-block metric data over the finite local-vertex
vocabulary. -/
def toIndexedTable
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    (M : CrossBlockMetricData P)
    (k : Nat) (hk : 0 < k) :
    IndexedCrossBlockMetricTable P k hk where
  lower := fun i u j v =>
    M.lower k hk i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
      j (CrossBlockLowerBoundsInterface.localVertexOfIndex v)
  lower_ge_one := by
    intro i u j v hij
    exact
      M.lower_ge_one k hk i
        (CrossBlockLowerBoundsInterface.localVertexOfIndex u) j
        (CrossBlockLowerBoundsInterface.localVertexOfIndex v) hij
  lower_bound := by
    intro i u j v hij
    simpa [indexedGeneratedPoint] using
      M.lower_bound k hk i
        (CrossBlockLowerBoundsInterface.localVertexOfIndex u) j
        (CrossBlockLowerBoundsInterface.localVertexOfIndex v) hij

/-- Existing cross-block metric data can be viewed as finite-index metric
tables for search and certificate extraction. -/
def toIndexedTableFamily
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    (M : CrossBlockMetricData P) :
    IndexedCrossBlockMetricTableFamily P where
  table := M.toIndexedTable

/-- Finite-index metric table families are exactly the same source
obligation as inhabiting the flexible cross-block metric data. -/
theorem nonempty_iff_indexedTables
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T} :
    Nonempty (CrossBlockMetricData P) <->
      Nonempty (IndexedCrossBlockMetricTableFamily P) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro M =>
        exact Nonempty.intro M.toIndexedTableFamily
  case mpr =>
    exact nonempty_of_indexedTables

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

/-! ## Eventual non-rigid metric route -/

/-- Thresholded finite period-search data for the eventual non-rigid
role-hinge route.  This is the positive replacement shape for searches that
only certify all sufficiently large block counts. -/
structure EventualPeriodSearchData
    (T : SameOppositeCandidate) (K0 : Nat) where
  word :
    forall (k : Nat), K0 <= k -> 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      ExactPeriodEquations T hk (word k hK hk)

namespace EventualPeriodSearchData

/-- Build the candidate-specific thresholded period-search data from the
generic thresholded finite-word family. -/
def ofThresholdPeriodWordFamily
    {T : SameOppositeCandidate} {K0 : Nat}
    (F :
      PeriodWordCertificates.ThresholdPeriodWordFamily
        T.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase K0) :
    EventualPeriodSearchData T K0 where
  word := F.word
  equation := F.equation

/-- Forget candidate-specific thresholded period-search data back to the
generic finite-word family. -/
def toThresholdPeriodWordFamily
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0) :
    PeriodWordCertificates.ThresholdPeriodWordFamily
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase K0 where
  word := P.word
  equation := P.equation

/-- The thresholded period-search source is precisely the generic
thresholded finite-word source, specialized to this candidate. -/
theorem nonempty_iff_thresholdPeriodWordFamily
    {T : SameOppositeCandidate} {K0 : Nat} :
    Nonempty (EventualPeriodSearchData T K0) <->
      Nonempty
        (PeriodWordCertificates.ThresholdPeriodWordFamily
          T.toFigure2TransitionObligations
          BaseTransitionRealization.exactBase K0) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toThresholdPeriodWordFamily
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro (ofThresholdPeriodWordFamily F)

/-- Raw generated-chain orientation for one thresholded period length. -/
def orientation
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  (P.word k hK hk).toFin

@[simp]
theorem orientation_apply
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) (i : Fin k) :
    P.orientation k hK hk i = P.word k hK hk i :=
  rfl

/-- Finite word projected to the period-search interface. -/
def finiteWord
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodSearchInterface.FiniteOrientationWord :=
  PeriodWordCertificates.finiteOrientationWordOfWord hk (P.word k hK hk)

@[simp]
theorem finiteWord_length
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    (P.finiteWord k hK hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) (i : Fin k) :
    (P.finiteWord k hK hk).letter i = P.orientation k hK hk i :=
  rfl

/-- Indexed algebraic certificate projected from the thresholded finite
equation fields. -/
def indexedCertificate
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      (P.finiteWord k hK hk) :=
  PeriodWordCertificates.indexedAlgebraicCertificateOfWord
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (P.word k hK hk)
    (P.equation k hK hk)

/-- Generated closure equation projected from the thresholded finite period
equations. -/
def closure
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hK hk) :=
  PeriodWordCertificates.generatedClosureEquationOfWord
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (P.word k hK hk)
    (P.equation k hK hk)

/-- Generated final-block period equation projected from the thresholded
finite period equations. -/
def periodEquation
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hK hk) :=
  PeriodWordCertificates.generatedPeriodEquationOfWord
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (P.word k hK hk)
    (P.equation k hK hk)

/-- Generated-period hypothesis projected from the thresholded finite period
equations. -/
def generatedPeriod
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hK hk) :=
  PeriodWordCertificates.generatedPeriodOfWord
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (P.word k hK hk)
    (P.equation k hK hk)

/-- Generated-chain family projected from a candidate and its thresholded
period data. -/
def toEventualGeneratedChainFamily
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0) :
    GeneratedSeparationInterface.EventualGeneratedChainFamily K0 where
  O := fun _k _hK _hk => T.toFigure2TransitionObligations
  base := fun _k _hK _hk => BaseTransitionRealization.exactBase
  orientation := P.orientation

@[simp]
theorem toEventualGeneratedChainFamily_O
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    (P.toEventualGeneratedChainFamily).O k hK hk =
      T.toFigure2TransitionObligations := by
  rfl

@[simp]
theorem toEventualGeneratedChainFamily_base
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    (P.toEventualGeneratedChainFamily).base k hK hk =
      BaseTransitionRealization.exactBase := by
  rfl

@[simp]
theorem toEventualGeneratedChainFamily_orientation
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    (P.toEventualGeneratedChainFamily).orientation k hK hk =
      P.orientation k hK hk := by
  rfl

/-- Period hypotheses for the thresholded generated-chain family. -/
def periods
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0) :
    P.toEventualGeneratedChainFamily.Periods := by
  intro k hK hk
  exact P.generatedPeriod k hK hk

end EventualPeriodSearchData

/-- The generated point addressed by the finite local-vertex index used by
thresholded metric-table search certificates. -/
def eventualIndexedGeneratedPoint
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    {k : Nat} (hK : K0 <= k) (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex) : R2 :=
  GeneratedClosedChain.generatedPoint
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase
    (P.orientation k hK hk) i
    (CrossBlockLowerBoundsInterface.localVertexOfIndex u)

/-- A finite-index cross-block metric table for one thresholded period length
in the non-rigid candidate surface. -/
structure EventualIndexedCrossBlockMetricTable
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) where
  lower : Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  lower_ge_one :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j -> 1 <= lower i u j v
  lower_bound :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j ->
          lower i u j v <=
            _root_.eucDist
              (eventualIndexedGeneratedPoint P hK hk i u)
              (eventualIndexedGeneratedPoint P hK hk j v)

namespace EventualIndexedCrossBlockMetricTable

/-- Interpret a thresholded finite-index metric table as a local-vertex lower
table. -/
def toLocalLower
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    {k : Nat} {hK : K0 <= k} {hk : 0 < k}
    (M : EventualIndexedCrossBlockMetricTable P k hK hk) :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real :=
  fun i u j v =>
    M.lower i (CrossBlockLowerBoundsInterface.localVertexIndex u) j
      (CrossBlockLowerBoundsInterface.localVertexIndex v)

/-- The finite-index `>= 1` row projects to the local-vertex cross-block
predicate used by generated separation. -/
theorem toLocalLower_ge_one
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    {k : Nat} {hK : K0 <= k} {hk : 0 < k}
    (M : EventualIndexedCrossBlockMetricTable P k hK hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      M.toLocalLower := by
  intro i u j v hij
  exact
    M.lower_ge_one i
      (CrossBlockLowerBoundsInterface.localVertexIndex u) j
      (CrossBlockLowerBoundsInterface.localVertexIndex v) hij

/-- The finite-index distance row projects to the local-vertex cross-block
metric predicate used by generated separation. -/
theorem toLocalLower_bound
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    {k : Nat} {hK : K0 <= k} {hk : 0 < k}
    (M : EventualIndexedCrossBlockMetricTable P k hK hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hK hk)
      M.toLocalLower := by
  intro i u j v hij
  simpa [toLocalLower, eventualIndexedGeneratedPoint] using
    M.lower_bound i
      (CrossBlockLowerBoundsInterface.localVertexIndex u) j
      (CrossBlockLowerBoundsInterface.localVertexIndex v) hij

end EventualIndexedCrossBlockMetricTable

/-- A family of finite-index metric tables, one for every thresholded period
length. -/
structure EventualIndexedCrossBlockMetricTableFamily
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0) where
  table :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      EventualIndexedCrossBlockMetricTable P k hK hk

namespace EventualIndexedCrossBlockMetricTableFamily

def lower
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    (M : EventualIndexedCrossBlockMetricTableFamily P)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real :=
  (M.table k hK hk).toLocalLower

theorem lower_ge_one
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    (M : EventualIndexedCrossBlockMetricTableFamily P)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      (M.lower k hK hk) :=
  (M.table k hK hk).toLocalLower_ge_one

theorem lower_bound
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    (M : EventualIndexedCrossBlockMetricTableFamily P)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hK hk)
      (M.lower k hK hk) :=
  (M.table k hK hk).toLocalLower_bound

end EventualIndexedCrossBlockMetricTableFamily

/-- Thresholded cross-block metric data for the eventual non-rigid route. -/
structure EventualCrossBlockMetricData
    {T : SameOppositeCandidate} {K0 : Nat}
    (P : EventualPeriodSearchData T K0) where
  lower :
    forall (k : Nat), K0 <= k -> 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
        (lower k hK hk)
  lower_bound :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase
        (P.orientation k hK hk)
        (lower k hK hk)

namespace EventualCrossBlockMetricData

/-- Build thresholded cross-block metric data from finite-index metric
tables. -/
def ofIndexedTables
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    (M : EventualIndexedCrossBlockMetricTableFamily P) :
    EventualCrossBlockMetricData P where
  lower := M.lower
  lower_ge_one := M.lower_ge_one
  lower_bound := M.lower_bound

/-- Finite-index thresholded metric table families inhabit the thresholded
cross-block metric-data surface. -/
theorem nonempty_of_indexedTables
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0} :
    Nonempty (EventualIndexedCrossBlockMetricTableFamily P) ->
      Nonempty (EventualCrossBlockMetricData P) := by
  intro h
  cases h with
  | intro M =>
      exact Nonempty.intro (ofIndexedTables M)

/-- Re-index thresholded cross-block metric data over the finite local-vertex
vocabulary. -/
def toIndexedTable
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    (M : EventualCrossBlockMetricData P)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    EventualIndexedCrossBlockMetricTable P k hK hk where
  lower := fun i u j v =>
    M.lower k hK hk i
      (CrossBlockLowerBoundsInterface.localVertexOfIndex u) j
      (CrossBlockLowerBoundsInterface.localVertexOfIndex v)
  lower_ge_one := by
    intro i u j v hij
    exact
      M.lower_ge_one k hK hk i
        (CrossBlockLowerBoundsInterface.localVertexOfIndex u) j
        (CrossBlockLowerBoundsInterface.localVertexOfIndex v) hij
  lower_bound := by
    intro i u j v hij
    simpa [eventualIndexedGeneratedPoint] using
      M.lower_bound k hK hk i
        (CrossBlockLowerBoundsInterface.localVertexOfIndex u) j
        (CrossBlockLowerBoundsInterface.localVertexOfIndex v) hij

/-- Existing thresholded cross-block metric data can be viewed as
finite-index metric tables for search and certificate extraction. -/
def toIndexedTableFamily
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    (M : EventualCrossBlockMetricData P) :
    EventualIndexedCrossBlockMetricTableFamily P where
  table := M.toIndexedTable

/-- Finite-index thresholded metric table families are exactly the same
source obligation as inhabiting the thresholded cross-block metric data. -/
theorem nonempty_iff_indexedTables
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0} :
    Nonempty (EventualCrossBlockMetricData P) <->
      Nonempty (EventualIndexedCrossBlockMetricTableFamily P) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro M =>
        exact Nonempty.intro M.toIndexedTableFamily
  case mpr =>
    exact nonempty_of_indexedTables

/-- Generated global separation projected from thresholded finite cross-block
lower-bound fields and candidate same-block metric data. -/
def separated
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    (M : EventualCrossBlockMetricData P)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hK hk) :=
  GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase
    (P.orientation k hK hk)
    (T.generatedSameBlockIsometry hk (P.orientation k hK hk))
    (M.lower k hK hk)
    (M.lower_ge_one k hK hk)
    (M.lower_bound k hK hk)

/-- Family-level metric hypotheses projected from thresholded finite
cross-block data. -/
def toEventualFamilyMetricHypotheses
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    (M : EventualCrossBlockMetricData P) :
    GeneratedSeparationInterface.EventualGeneratedChainFamily.MetricHypotheses
      P.toEventualGeneratedChainFamily where
  metric := fun k hK hk =>
    T.generatedMetricHypotheses hk (P.orientation k hK hk)
      (M.separated k hK hk)

/-- Thresholded period and cross-block metric data give explicit closed
placement certificates from the selected block threshold onward. -/
def explicitClosedPlacementCertificate
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    (M : EventualCrossBlockMetricData P)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk :=
    (GeneratedClosedChainReduction.explicitTransitionClosedPlacementCertificateOfGenerated
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase
    (P.orientation k hK hk)
    (P.generatedPeriod k hK hk)
    (M.separated k hK hk)
    (T.generatedSameBlockIsometry hk (P.orientation k hK hk)))
    |>.toExplicitClosedPlacementCertificate

/-- Thresholded period and cross-block metric data give every vertex target
from the explicit threshold `16 * K0` onward. -/
theorem targetUpperConstructionFiveSixteenAt_large
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    (M : EventualCrossBlockMetricData P)
    {n : Nat} (hn : 16 * K0 <= n) :
    targetUpperConstructionFiveSixteenAt n := by
  have hr : n % 16 < 16 := by
    exact Nat.mod_lt n (by norm_num)
  have hn_split : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  have hAt :
      targetUpperConstructionFiveSixteenAt
        (16 * (n / 16) + n % 16) := by
    by_cases hk : 0 < n / 16
    case pos =>
      have hK : K0 <= n / 16 := by
        omega
      exact
        RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
          hr
          (ClosedChainReduction.exactChainUpperOfExplicitClosedPlacementCertificate
            (M.explicitClosedPlacementCertificate (n / 16) hK hk))
          (SplitSoundness.remainderUpperOfConstruction (n % 16))
    case neg =>
      have hk0 : n / 16 = 0 := Nat.eq_zero_of_not_pos hk
      have hzero :
          targetUpperConstructionFiveSixteenAt (16 * 0 + n % 16) :=
        RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
          hr
          SplitSoundness.emptyExactChainUpper
          (SplitSoundness.remainderUpperOfConstruction (n % 16))
      simpa [hk0] using hzero
  rw [hn_split]
  exact hAt

/- Thresholded period and cross-block metric data give the source-faithful
eventual Pach--Toth target. -/
set_option linter.style.longLine false in
theorem targetUpperConstructionFiveSixteenEventually
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    (M : EventualCrossBlockMetricData P) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  exact
    ClosedChainReduction.targetUpperConstructionFiveSixteenEventually_of_eventualExplicitClosedPlacementCertificates
      K0 M.explicitClosedPlacementCertificate

/-- With a matching finite complement below `16 * K0`, thresholded period and
cross-block metric data give the arbitrary-`n` target through the eventual
route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_smallUpTo
    {T : SameOppositeCandidate} {K0 : Nat}
    {P : EventualPeriodSearchData T K0}
    (M : EventualCrossBlockMetricData P)
    (Hsmall : targetUpperConstructionFiveSixteenSmallUpTo (16 * K0)) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
      (16 * K0)
      (fun n hn => M.targetUpperConstructionFiveSixteenAt_large hn)
      Hsmall

end EventualCrossBlockMetricData

/-- The positive thresholded non-rigid/generated metric route for a fixed
candidate: period words plus cross-block metric tables from the same
threshold onward. -/
structure EventualPositiveRouteData
    (T : SameOppositeCandidate) (K0 : Nat) where
  period : EventualPeriodSearchData T K0
  metric : EventualCrossBlockMetricData period

namespace EventualPositiveRouteData

/-- The route package gives the source-faithful eventual Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteenEventually
    {T : SameOppositeCandidate} {K0 : Nat}
    (R : EventualPositiveRouteData T K0) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  R.metric.targetUpperConstructionFiveSixteenEventually

/-- Nonempty route data is enough to close the eventual target. -/
theorem targetUpperConstructionFiveSixteenEventually_of_nonempty
    {T : SameOppositeCandidate} {K0 : Nat}
    (H : Nonempty (EventualPositiveRouteData T K0)) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  cases H with
  | intro R =>
      exact R.targetUpperConstructionFiveSixteenEventually

end EventualPositiveRouteData

/-- Candidate-free packaging for a chosen thresholded positive route. -/
structure ChosenEventualPositiveRouteData (K0 : Nat) where
  candidate : SameOppositeCandidate
  period : EventualPeriodSearchData candidate K0
  metric : EventualCrossBlockMetricData period

namespace ChosenEventualPositiveRouteData

/-- A chosen thresholded route gives the source-faithful eventual
Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (R : ChosenEventualPositiveRouteData K0) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  R.metric.targetUpperConstructionFiveSixteenEventually

theorem targetUpperConstructionFiveSixteenEventually_of_nonempty
    {K0 : Nat} (H : Nonempty (ChosenEventualPositiveRouteData K0)) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  cases H with
  | intro R =>
      exact R.targetUpperConstructionFiveSixteenEventually

end ChosenEventualPositiveRouteData

end

end RoleHingeCandidateSearchSurface
end PachToth
end ErdosProblems1066
